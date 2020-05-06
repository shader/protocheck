from protocheck.bspl import load_file
import os
import configargparse
import simplejson as json
import random

parser = configargparse.get_argument_parser()
parser.add('-o', '--output', default="flows.json",
           help="Path to json file for storing node red flows")
parser.add('--append', default=False,
           help="Append nodes to json file; default is to overwrite")

roles = {}
base_port = 8000


def get_role_index(name):
    if roles.get(name, -1) == -1:
        roles[name] = len(roles)
    return roles[name]


def get_port(role, base_port=base_port):
    return base_port + get_role_index(role.name)


def node_id():
    return '{:08x}.{:06x}'.format(random.randrange(16**8), random.randrange(16**6))


def create_role_tab(role):
    tab = {
        "id": node_id(),
        "type": "tab",
        "label": role.name,
        "disabled": False,
        "info": ""
    }
    return tab


def udp_in_node(role, base_port=base_port):
    return {
        "id": node_id(),
        "type": "udp in",
        "name": role.name,
        "iface": "",
        "port": get_port(role, base_port=base_port),
        "ipv": "udp4",
        "multicast": "false",
        "group": "",
        "datatype": "utf8",
    }


def udp_out_node(addr="localhost", base_port=base_port):
    return {
        "id": node_id(),
        "type": "udp out",
        "name": "outgoing UDP",
        "iface": "",
        "addr": addr,
        "port": None,
        "ipv": "udp4",
        "outport": "",
        "multicast": "false",
        "base64": False,
        "datatype": "utf8",
    }


def json_node(name="", offset=None):
    node = {
        "id": node_id(),
        "type": "json",
        "name": name,
        "property": "payload",
        "action": "",
        "pretty": False,
    }
    if offset:
        node["offset"] = offset
    return node


def debug_payload(name=""):
    return {
        "id": node_id(),
        "type": "debug",
        "name": name,
        "active": True,
        "tosidebar": True,
        "console": False,
        "tostatus": False,
        "complete": "payload",
        "targetType": "msg",
        "width": 60
    }


def connect(source, dest):
    if "wires" in source:
        source["wires"][0].push(dest["id"])
    else:
        source["wires"] = [[dest["id"]]]


def connect_nodes(nodes):
    for i in range(len(nodes)):
        if i > 0:
            connect(nodes[i - 1], nodes[i])


def parameter_string(parameters, adornment=True):
    return ", ".join([p.format(adornment=adornment) for p in parameters])


def bspl_incoming(role, parameters, sending=True):
    return {
        "id": node_id(),
        "type": "bspl-incoming",
        "name": "Check " + role + " incoming",
        "timeout": 0,
        "spec": parameter_string(parameters, adornment=False),
        "width": len(role) * 5 + 60
    }


def message_specs(sent_messages):
    specs = []
    for msg in sent_messages:
        params = parameter_string(msg.parameters.values())
        recipient = msg.recipient.name
        port = get_port(msg.recipient)
        specs.append(params + " -> " + recipient + ":" + str(port))
    return specs


def bspl_outgoing(role, sent_messages, sending=True):
    name = "Check " + role.name + " outgoing"
    return {
        "id": node_id(),
        "type": "bspl-outgoing",
        "name": name,
        "spec": "\n".join(message_specs(sent_messages)),
        "width": 50 + len(name) * 5
    }


def inject(message):
    parameters = {
        p for p in message.parameters.values() if p.adornment in ["out", "in"]}
    name = "inject " + message.shortname
    return {
        "id": node_id(),
        "type": "inject",
        "name": name,
        "topic": "",
        "payload": json.dumps({p.name: p.name for p in parameters}),
        "payloadType": "json",
        "repeat": "",
        "crontab": "",
        "once": False,
        "onceDelay": 0.1,
        "width": 60 + len(name) * 5
    }


def incoming_nodes(role, spec):
    nodes = [udp_in_node(role),
             json_node(),
             bspl_incoming(role.name, spec),
             debug_payload(role.name)]
    connect_nodes(nodes)
    return nodes


def outgoing_nodes(role, sent_messages):
    nodes = [
        bspl_outgoing(role, sent_messages),
        json_node(offset=50),
        udp_out_node()
    ]
    connect_nodes(nodes)
    return nodes


def place(tab, nodes):
    offset = (70, 60)
    rows = 1

    backwires = {}
    node_map = {}
    for n in nodes:
        node_map[n['id']] = n
        if n.get('wires'):
            for w in n['wires'][0]:
                if backwires.get(w):
                    backwires[w].append(n['id'])
                else:
                    backwires[w] = [n['id']]

    for n in nodes:
        n['z'] = tab['id']
        if backwires.get(n['id']):
            prev = node_map[backwires[n['id']][0]]
            n['x'] = prev['x'] + (100 + prev['width'] / 2
                                  if prev.get('width') else 140)
            n['y'] = prev['y']
        else:
            n['x'] = offset[0]
            n['y'] = offset[1] * rows
            rows += 1
        n['x'] += n.get('width', 0) / 2 + n.get('offset', 0)

    for n in nodes:
        if "width" in n:
            del n["width"]
        if "offset" in n:
            del n["offset"]


def handle_node_flow(args):
    spec = load_file(args.input[0])
    path = args.input[1] if len(args.input) > 1 else args.output
    if args.append:
        try:
            with open(path, 'r') as file:
                nodes = json.load(file)
        except:
            nodes = []
    else:
        nodes = []

    messages = {role: [m for m in spec.messages
                       if m.sender == role or m.recipient == role]
                for role in spec.roles.values()}
    sent_messages = {role: [m for m in spec.messages if m.sender == role]
                     for role in spec.roles.values()}

    roles = sorted(set(r for r in spec.roles.values() if len(messages[r])),
                   key=lambda r: len(
                       [m for m in messages[r] if m.sender == r]),
                   reverse=True)
    for role in roles:
        parameters = {p.name: p for m in messages[role]
                      for p in m.parameters.values()}
        tab = create_role_tab(role)
        role_nodes = incoming_nodes(role, parameters.values())

        msg_nodes = [inject(message)
                     for message in sent_messages[role]]
        role_nodes.extend(msg_nodes)

        outgoing = outgoing_nodes(role, sent_messages[role])

        for msg in msg_nodes:
            connect_nodes([msg, outgoing[0]])
        role_nodes.extend(outgoing)

        place(tab, role_nodes)
        nodes.append(tab)
        nodes.extend(role_nodes)

    with open(path, 'w') as file:
        json.dump(nodes, file)
