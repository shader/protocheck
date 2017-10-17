#!/usr/bin/env python
import time
import boolexpr as bx
from boolexpr import and_, impl, or_, onehot, and_s
from itertools import combinations, permutations, chain
import re
import configargparse
from protocheck import logic

arg_parser = configargparse.get_argument_parser()
arg_parser.add("-t", "--tseytin", action="store_true")
arg_parser.add("-e", "--exhaustive", action="store_true")
arg_parser.add("-d", "--depth", default=1, help="Longest transitive relationship to generate. \
Only need log2(max-chain) to prevent cycles.")
ctx = bx.Context()
aux = bx.Context()
flatten = chain.from_iterable
stats = {"size": 0, "degree": 0, "statements": 0}


def reset_stats():
    stats["size"] = 0
    stats["degree"] = 0
    stats["statements"] = 0
    stats["time"] = 0


def name(var):
    "convert name or var to name"
    if hasattr(var, 'name'):
        return var.name
    if hasattr(var, 'get') and var.get('name', None):
        return var.get('name')
    return str(var)


def var(n):
    "convert name or var to var"
    if type(n) == bx.wrap.Variable:
        return n
    return ctx.get_var(n)


def wrap(fn):
    "Apply function to all arguments on a function"
    def wrapper(target):
        def transform(*args):
            return target(*map(lambda a: fn(a), args))
        return transform
    return wrapper


def pair(a, b):
    return tuple(sorted((a, b)))


def pairs(xs):
    return combinations(xs, 2)


def pairwise(fn, xs):
    return list(map(lambda p: fn(*p), pairs(xs)))


@wrap(name)
def sequential(a, b, *rest):
    if rest:
        return and_(*pairwise(sequential, (a, b) + rest))
    return var(a + "<" + b)


@wrap(name)
def simultaneous(a, b, *rest):
    if rest:
        return and_(*pairwise(simultaneous, (a, b) + rest))

    a, b = sorted((a, b))  # make sure we always use pairs in the same order
    return var(a + "*" + b)


@wrap(var)
def ordered(*args):
    "Arguments happen in some order; not simultaneously"
    return and_(*pairwise(lambda a, b: ~a | ~b
                          | sequential(a, b)
                          | sequential(b, a),
                          args))


def causal(event, causes):
    event = var(event)
    expr = ~event
    for c in causes:
        expr = expr | simultaneous(event, c)
    return expr


relation = {
    '<': sequential,
    '*': simultaneous,
    '>': lambda a, b: sequential(b, a)
}


def relationships(statements):
    inputs = flatten([s.support() for s in statements])
    rs = {}
    for i in inputs:
        s = re.search('[<.*]', name(i))
        if s:
            rel = s.group()
            t = tuple(name(i).split(rel))
            p = pair(*t)
            if rel == '<' and t != p:
                rel = '>'

            if p in rs:
                rs[p].add(rel)
            else:
                rs[p] = {rel}
    return rs


def timeline(relationships):
    """A timeline is linear, and allows only a single relationship
    between each pair of events; a<b, b<a, or a*b"""
    clauses = []
    for pair, rels in relationships.items():
        clauses.append(impl(var(pair[0]) & var(pair[1]),
                            onehot(*[relation[rel](*pair) for rel in rels])))
    return clauses


def occurrence(relationships):
    clauses = []
    for pair, rels in relationships.items():
        for r in rels:
            clauses.append(impl(relation[r](*pair), var(pair[0]) & var(pair[1])))
    return clauses


def invert(relationships):
    inverses = {"*": "*",
                ">": "<",
                "<": ">"}
    return set(map(lambda r: inverses[r], relationships))


def normalize(p, relationships):
    n = pair(*p)
    if n == p:
        return p, relationships
    else:
        # must have been backwards; invert relationships
        return n, invert(relationships)


def pivot(a, b):
    """Given (a, b) and (b, c), returns b"""
    intersection = set(a) & set(b)
    if intersection:
        return intersection.pop()


def antipivot(a, b):
    """Given (a, b) and (b, c), returns a"""
    intersection = set(a) - set(b)
    if intersection:
        return intersection.pop()


def outer(a, b):
    r = antipivot(a, b)
    s = antipivot(b, a)
    if r and s:
        return (r, s)


def align(a, b):
    """Given (a, b) and (c, b), returns ((a, b), (b, c))"""
    p = pivot(a, b)
    if not p:
        return None, None
    o = pair(*outer(a, b))
    return (o[0], p), (p, o[1])


def match(new, old, rels):
    if new != old:
        return invert(rels)
    return rels


def triples(relationships):
    triples = {}
    pairs = relationships.keys()
    for r in pairs:
        for s in pairs:
            if r is not s and pivot(r, s):
                a, b = align(r, s)
                if antipivot(a, b) in r:
                    triples[a + b[1:]] = (match(a, r, relationships[r]),
                                          match(b, s, relationships[s]))
                else:
                    triples[a + b[1:]] = (match(a, s, relationships[s]),
                                          match(b, r, relationships[r]))
    return triples


def transitivity(triples):
    clauses = []
    for triple, (rels_a, rels_b) in triples.items():
        a = (triple[0], triple[1])
        b = (triple[1], triple[2])
        o = (triple[0], triple[2])
        for rel_a in rels_a:
            for rel_b in rels_b:
                if rel_a == "*":
                    clauses.append(impl(simultaneous(*a) & relation[rel_b](*b),
                                        relation[rel_b](*o)))
                elif rel_b == "*" or rel_b == rel_a:
                    clauses.append(impl(relation[rel_a](*a) & relation[rel_b](*b),
                                        relation[rel_a](*o)))
    return clauses


def consistency(statements):
    rels = relationships(statements)
    c = timeline(rels)
    c += occurrence(relationships(c))
    c += transitivity(triples(relationships(c)))
    c += timeline(relationships(c))
    c += occurrence(relationships(c))
    return c


def extract_events(statements):
    inputs = flatten([s.support() for s in statements])
    return set(flatten([re.split('[<.*]', name(i)) for i in inputs]))


def transitive(fn):
    def inner(a, b, c):
        return and_(impl(fn(a, b) & fn(b, c), fn(a, c)),
                    impl(simultaneous(a, b) & fn(b, c), fn(a, c)),
                    impl(fn(a, b) & simultaneous(b, c), fn(a, c)))
    return inner


def exhaustive_transitivity(events):
    "Simultanaeity and sequentiality are transitive properties"
    clauses = []
    sim = transitive(simultaneous)
    seq = transitive(sequential)

    clauses.extend([sim(*tup) for tup in combinations(events, 3)])
    clauses.extend([seq(*tup) for tup in permutations(events, 3)])

    return clauses


@wrap(var)
def exhaustive_occurrence(*events):
    "Relationships between events imply that the events themselves occur"
    return pairwise(lambda a, b: impl(or_(simultaneous(a, b),
                                          sequential(a, b),
                                          sequential(b, a)),
                                      a & b),
                    events)


@wrap(var)
def exhaustive_timeline(*events):
    """
    A timeline is linear, and allows only a single relationship between
    each pair of events; a<b, b<a, or a*b
    """
    return pairwise(lambda a, b: impl(a & b, onehot(simultaneous(a, b),
                                                    sequential(a, b),
                                                    sequential(b, a))), events)


def exhaustive_consistency(statements):
    events = extract_events(statements)
    return exhaustive_timeline(*events) \
        + exhaustive_occurrence(*events) \
        + exhaustive_transitivity(events)


def cycle(enactment):
    def add(s, k, v):
        if k not in s:
            s[k] = {v}
        else:
            s[k].add(v)

    follows = {}
    precedes = {}

    def propagate(item, start, step, acc):
        def inner(current, queue=set(), visited=set()):
            add(acc, current, item)
            visited.add(current)
            queue = queue.union(step.get(current, set())) - visited
            if queue:
                inner(queue.pop(), queue, visited)
        inner(start)

    for e in enactment:
        e = name(e)
        if '<' in e:
            a, b = e.split('<')
            if b in precedes.get(a, []):
                return precedes[a].union({a})
            else:
                propagate(a, b, follows, precedes)

            if a in follows.get(b, []):
                return follows[b].union({b})
            else:
                propagate(b, a, precedes, follows)


def solve(clauses, options=None, depth=None):
    formula = and_s(*clauses)
    if options and options.tseytin:
        formula = formula.tseytin(aux)

    stats["size"] += formula.size()
    stats["degree"] = max(stats["degree"], formula.degree())
    if options and options.verbose:
        s = {"size": formula.size(), "degree": formula.degree()}
        if depth:
            s["depth"] = depth
        print(s)

    result = formula.sat()[1]
    if result:
        return [k for k, v in result.items() if v]


def consistent(*statements, exhaustive=False):
    options = arg_parser.parse_known_args()[0]  # apparently returns a tuple
    stats["statements"] += logic.count(statements)
    statements = [logic.compile(s) for s in statements]

    clauses = statements
    start = time.clock()
    if options.exhaustive or exhaustive:
        clauses += exhaustive_consistency(statements)
        result = solve(clauses, options, depth="exhaustive")
    else:
        depth = int(options.depth)
        for d in range(depth):
            clauses += consistency(clauses)
        result = solve(clauses, options, depth)
        while result and cycle(result):
            depth += 1
            clauses += consistency(clauses)
            result = solve(clauses, options, depth)
    stop = time.clock()
    stats["time"] += stop - start

    return result
