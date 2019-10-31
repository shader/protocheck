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


def get_role_port(name):
    if not roles.get(name):
        roles[name] = len(roles)
    return roles[name]


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
        "port": base_port + get_role_port(role.name),
        "ipv": "udp4",
        "multicast": False,
        "group": "",
        "datatype": "utf8",
    }


def udp_out_node(role, addr="localhost", base_port=base_port):
    return {
        "id": node_id(),
        "type": "udp out",
        "name": "to " + role.name,
        "iface": "",
        "addr": addr,
        "port": base_port + get_role_port(role.name),
        "ipv": "udp4",
        "outport": "",
        "multicast": False,
        "base64": False,
        "datatype": "utf8",
    }


def json_node(name=""):
    return {
        "id": node_id(),
        "type": "json",
        "name": name,
        "property": "payload",
        "action": "",
        "pretty": False,
    }


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
        "targetType": "msg"
    }


def connect(source, dest):
    if "wires" in source:
        if len(dest["wires"]) > 0:
            source["wires"][0].push(dest["id"])
        else:
            source["wires"] = [dest["id"]]
    else:
        source["wires"] = [dest["id"]]


def connect_nodes(nodes):
    for i in range(len(nodes)):
        if i > 0:
            connect(nodes[i - 1], nodes[i])


def parameter_string(parameters):
    return ", ".join([p.format() for p in parameters])


def bspl_message(message, sending=True):
    name = "send " + message.name
    return {
        "id": node_id(),
        "type": "bspl-message",
        "name": name,
        "spec": parameter_string(message.parameters.values()),
        "width": 50 + len(name) * 5
    }


def bspl_observer(role, parameters, sending=True):
    return {
        "id": node_id(),
        "type": "bspl-observer",
        "name": role,
        "timeout": 60000,
        "spec": parameter_string(parameters),
        "width": len(role) * 5 + 60
    }


def inject(parameters):
    parameters = {p for p in parameters if p.adornment == "out" or p.key}
    return {
        "id": node_id(),
        "type": "inject",
        "name": "",
        "topic": "",
        "payload": json.dumps({p.name: p.name for p in parameters}),
        "payloadType": "json",
        "repeat": "",
        "crontab": "",
        "once": False,
        "onceDelay": 0.1,
        "width": 60
    }


def entry_nodes(role, spec):
    nodes = [udp_in_node(role),
             json_node(),
             bspl_observer(role.name, spec),
             debug_payload(role.name)]
    connect_nodes(nodes)
    return nodes


def out_nodes(role, message):
    nodes = [
        inject(message.parameters.values()),
        bspl_message(message, sending=True),
        json_node(),
        udp_out_node(message.recipient)
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
            for w in n['wires']:
                if backwires.get(w):
                    backwires[w].append(n['id'])
                else:
                    backwires[w] = [n['id']]

    for n in nodes:
        n['z'] = tab['id']
        if backwires.get(n['id']):
            prev = node_map[backwires[n['id']][0]]
            n['x'] = n.get('width', 0) / 2 + prev['x'] + \
                (100 + prev['width'] / 2 if prev.get('width') else 140)
            n['y'] = prev['y']
        else:
            n['x'] = offset[0] + n.get('width', 0) / 2
            n['y'] = offset[1] * rows
            rows += 1

    for n in nodes:
        if "width" in n:
            del n["width"]


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

    for role in set(spec.roles.values()):
        parameters = {
            p for m in spec.messages for p in m.parameters.values()
            if m.sender == role or m.recipient == role}
        tab = create_role_tab(role)
        role_nodes = entry_nodes(role, parameters)

        for message in spec.messages:
            if message.sender == role:
                role_nodes.extend(out_nodes(role, message))

        place(tab, role_nodes)
        nodes.append(tab)
        nodes.extend(role_nodes)

    with open(path, 'w') as file:
        json.dump(nodes, file)
