#!/usr/bin/env python
import os
import sys
import boolexpr as bx
from boolexpr import *
from itertools import combinations, permutations, chain
import re
import configargparse

p = configargparse.get_argument_parser()
p.add("-t", "--tseytin", action="store_true")
p.add("-g", "--group-events", action="store_true")
options = p.parse_known_args()

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

def pairs(xs):
    return combinations(xs, 2)

def pairwise(fn, xs):
    return map(lambda p: fn(*p), pairs(xs))

@wrap(name)
def sequential(a, b, *rest):
    if rest:
        return and_(*pairwise(sequential, args))
    return var(a + ">" + b)

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

@wrap(var)
def timeline(*events):
    "A timeline is linear, and allows only a single relationship between each pair of events; a>b, b>a, or a*b"
    return and_(
        *pairwise(lambda a,b: impl(a & b, onehot(simultaneous(a,b),
                                               sequential(a,b),
                                               sequential(b,a))), events)
    )

@wrap(var)
def occurrence(*events):
    "Relationships between events imply that the events themselves occur"
    return and_(*pairwise(lambda a,b: impl(or_(simultaneous(a,b),
                                               sequential(a,b),
                                               sequential(b,a)),
                                           a & b),
                          events))

flatten = chain.from_iterable

def transitive(fn):
    def inner(a,b,c):
        return impl(fn(a,b) & fn(b,c), fn(a,c))
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
    return set(flatten([re.split('[>.*]', name(i)) for i in inputs]))

def group_events(events):
    grouped = {}
    for e in events:
        role, event = re.split(':', e)
        if role in grouped:
            grouped[role].append(e)
        else:
            grouped[role] = [e]
    return grouped

def consistency(*events):
    return and_(timeline(*events),
                occurrence(*events),
                transitivity(*events))

def consistent(*statements):
    events = extract_events(*statements)

    clauses = []
    if options.group_events:
        groups = group_events(events)

        for role in groups:
            es = groups[role]
            clause = consistency(*es)
            clauses.append(clause)
    else:
        clauses.append(consistency(*events))

    formula = and_(*(clauses + list(statements)))
    if options.tseytin:
        formula = formula.tseytin(aux)
    return formula
