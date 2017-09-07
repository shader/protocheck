#!/usr/bin/env python
import os
import sys
import boolexpr as bx
from boolexpr import *
from itertools import combinations, permutations, chain
import re
import configargparse
from protocheck import logic

arg_parser = configargparse.get_argument_parser()
arg_parser.add("-t", "--tseytin", action="store_true")
arg_parser.add("-g", "--group-events", action="store_true")

stats = {"size": 0, "degree": 0, "statements": 0}
def reset_stats():
    stats["size"] = 0
    stats["degree"] = 0
    stats["statements"] = 0

ctx = bx.Context()
aux = bx.Context()

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
    return map(lambda p: fn(*p), pairs(xs))

@wrap(name)
def sequential(a, b, *rest):
    if rest:
        return and_(*pairwise(sequential, args))
    return var(a + "<" + b)

@wrap(name)
def simultaneous(a, b, *rest):
    if rest:
        return and_(*pairwise(simultaneous, args))
    
    a,b = sorted((a,b)) #make sure we always use pairs in the same order
    return var(a+ "*" +b)

@wrap(var)
def ordered(*args):
    "Arguments happen in some order; not simultaneously"
    expr = or_(*[~v for v in args])
    return or_(expr, *pairwise(lambda a,b: sequential(a,b) | sequential(b,a), args))

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

@wrap(var)
def timeline(*events):
    "A timeline is linear, and allows only a single relationship between each pair of events; a<b, b<a, or a*b"
    return and_(
        *pairwise(lambda a,b: impl(a & b, onehot(simultaneous(a,b),
                                               sequential(a,b),
                                               sequential(b,a))), events)
    )

def occurrence(relationships):
    clauses = []
    for pair in relationships.keys():
        for r in relationships[pair]:
            clauses.append(impl(relation[r](*pair), var(pair[0]) & var(pair[1])))
    return and_(*clauses)

flatten = chain.from_iterable

def transitive(fn):
    def inner(a,b,c):
        return and_(impl(fn(a,b) & fn(b,c), fn(a,c)),
                    impl(simultaneous(a,b) & fn(b,c), fn(a,c)),
                    impl(fn(a,b) & simultaneous(b,c), fn(a,c)))
    return inner

def transitivity(*events):
    "Simultanaeity and sequentiality are transitive properties"
    clauses = []
    sim = transitive(simultaneous)
    seq = transitive(sequential)

    clauses.extend([sim(*tup) for tup in combinations(events, 3)])
    clauses.extend([seq(*tup) for tup in permutations(events, 3)])

    return and_s(*clauses)

def extract_events(*statements):
    inputs = flatten([s.support() for s in statements])
    return set(flatten([re.split('[<.*]', name(i)) for i in inputs]))

def group_events(events):
    grouped = {}
    for e in events:
        role, event = re.split(':', e)
        if role in grouped:
            grouped[role].append(e)
        else:
            grouped[role] = [e]
    return grouped


def consistency(relationships, *events):
    return and_(timeline(*events),
                occurrence(relationships),
                transitivity(*events))


def consistent(*statements):
    options = arg_parser.parse_known_args()[0]  # apparently returns a tuple
    stats["statements"] += logic.count(statements)
    statements = [logic.compile(s) for s in statements]

    rels = relationships(statements)
    events = extract_events(*statements)

    clauses = []
    if options.group_events:
        groups = group_events(events)

        for role in groups:
            es = groups[role]
            clause = consistency(rels, *es)
            clauses.append(clause)
    else:
        clauses.append(consistency(rels, *events))

    formula = and_(*(clauses + list(statements)))
    if options.tseytin:
        formula = formula.tseytin(aux)

    stats["size"] += formula.size()
    stats["degree"] = max(stats["degree"], formula.degree())
    return formula
