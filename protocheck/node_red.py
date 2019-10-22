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


def add_role(name):
    roles[name] = len(roles)


def node_id():
    return '{:08x}.{:06x}'.format(random.randrange(16**8), random.randrange(16**6))


def create_role_tab(protocol, role):
    tab = {
        "id": node_id(),
        "type": "tab",
        "label": protocol.name + " - " + role.name,
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
        "port": base_port + roles[role.name],
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
        "port": base_port + roles[role.name],
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


def parameter_string(protocol):
    return ", ".join([p.format() for p in protocol.parameters.values()])


def bspl_message(message, sending=True):
    return {
        "id": node_id(),
        "type": "bspl-message",
        "name": "send " + message.name,
        "spec": parameter_string(message),
        "width": 100
    }


def bspl_observer(role, protocol, sending=True):
    return {
        "id": node_id(),
        "type": "bspl-observer",
        "name": protocol.name + " " + role,
        "timeout": 60000,
        "spec": parameter_string(protocol),
        "width": 40
    }


def place(tab, nodes):
    pass


def entry_nodes(role, spec):
    nodes = [udp_in_node(role),
             json_node(),
             bspl_observer(role.name, spec),
             debug_payload(role.name)]
    connect_nodes(nodes)
    return nodes


def out_nodes(role, message):
    nodes = [
        bspl_message(message, sending=True),
        json_node(),
        udp_out_node(role)
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
            n['x'] = n.get('width', 0) + prev['x'] + 140 + \
                (prev['width'] if prev.get('width') else 0)
            n['y'] = prev['y']
        else:
            n['x'] = offset[0] + n.get('width', 0)
            n['y'] = offset[1] * rows
            rows += 1


def handle_node_flow(protocol, args):
    path = args.output
    if args.append:
        try:
            with open(path, 'r') as file:
                nodes = json.load(file)
        except:
            nodes = []
    else:
        nodes = []

    for role in protocol.roles.values():
        add_role(role.name)
        projection = protocol.projection(role)
        if not projection:
            break
        tab = create_role_tab(protocol, role)
        role_nodes = entry_nodes(role, projection)

        for message in protocol.messages.values():
            if message.sender == role:
                role_nodes.extend(out_nodes(role, message))

        place(tab, role_nodes)
        nodes.append(tab)
        nodes.extend(role_nodes)

    with open(path, 'w') as file:
        json.dump(nodes, file)

    # in case we're processing multiple protocols at once, append the rest of them
    args.append = True
