#!/usr/bin/env python
import os
import sys
import pyeda
from itertools import combinations, permutations, chain
import re
from pyeda.inter import *

def name(var):
    "convert name or var to name"
    if hasattr(var, 'name'):
        return var.name
    if 'name' in var:
        return var['name']
    return var

def var(n):
    "convert name or var to var"
    if type(n) == pyeda.boolalg.expr.Variable:
        return n
    return exprvar(n)

def wrap(fn):
    "Apply function to all arguments on a function"
    def wrapper(target):
        def transform(*args):
            return target(*map(lambda a: fn(a), args))
        return transform
    return wrapper

def pairs(xs):
    return combinations(xs, 2)

@wrap(name)
def sequential_pair(a, b):
    return var(a + ">" + b)

@wrap(name)
def simultaneous_pair(a, b):
    return var(a+"*"+b)

def pairwise(fn, xs):
    return map(lambda p: fn(*p), pairs(xs))

def sequential(*args):
    "Arguments occur sequentially"
    return And(*pairwise(sequential_pair, args))

def simultaneous(*args):
    "All arguments are pairwise simultaneous"
    return And(*pairwise(simultaneous_pair, sorted(args)))

@wrap(var)
def ordered(*args):
    "Arguments happen in some order; not simultaneously"
    expr = Or(*[~v for v in args])
    return Or(expr, *pairwise(lambda a,b: sequential(a,b) | sequential(b,a), args))

def causal(event, causes):
    event = var(event)
    expr = ~event
    for c in causes:
        expr = expr | simultaneous(event, c)
    return expr

@wrap(var)
def timeline(*events):
    "A timeline is linear, and allows only a single relationship between each pair of events; a>b, b>a, or a*b"
    return And(
        *pairwise(lambda a,b: ~a | ~b | OneHot(simultaneous_pair(a,b), sequential_pair(a,b), sequential_pair(b,a)), events)
    )

@wrap(var)
def occurrence(*events):
    "Relationships between events imply that the events themselves occur"
    return And(
        And(*pairwise(lambda a,b: Implies(simultaneous_pair(a,b), a&b), events)), #a*b => a & b
        And(*pairwise(lambda a,b: Implies(sequential_pair(a,b), a&b), events)), #a>b => a & b
        And(*pairwise(lambda a,b: Implies(sequential_pair(b,a), a&b), events)) #b>a => a & b
    )

flatten = chain.from_iterable

def transitive(fn):
    def inner(a,b,c):
        return Implies(fn(a,b) & fn(b,c), fn(a,c))
    return inner

def transitivity(*events):
    "Simultanaeity and sequentiality are transitive properties"
    sim = transitive(simultaneous)
    seq = transitive(sequential)
    return And(*flatten([sim(*tup) + seq(*tup) for tup in permutations(events, 3)]))

def extract_events(*statements):
    inputs = flatten([s.inputs for s in statements])
    return set(flatten([re.split('[>.*]', i.name) for i in inputs]))

def consistent(*statements):
    events = extract_events(*statements)
    return And(timeline(*events), occurrence(*events), transitivity(*events), *statements)
