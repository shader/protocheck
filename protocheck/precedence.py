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

stats = {"size": 0, "degree": 0, "statements": 0}
def reset_stats():
    stats["size"] = 0
    stats["degree"] = 0
    stats["statements"] = 0

ctx = bx.Context()
aux = bx.Context()
flatten = chain.from_iterable


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


def timeline(relationships):
    """A timeline is linear, and allows only a single relationship
    between each pair of events; a<b, b<a, or a*b"""
    clauses = []
    for pair in relationships.keys():
        clauses.append(impl(var(pair[0]) & var(pair[1]),
                            onehot(*[relation[rel](*pair) for rel in relationships[pair]])))
    return clauses


def occurrence(relationships):
    clauses = []
    for pair in relationships.keys():
        for r in relationships[pair]:
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
    o = outer(a, b)
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
            o = outer(r, s)
            if r is not s and pivot(r, s) and o in relationships:
                a, b = align(r, s)
                triples[a + b[1:]] = (match(a, r, relationships[r]),
                                      match(b, s, relationships[s]))
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


def consistency(relationships):
    return timeline(relationships) \
        + occurrence(relationships) \
        + transitivity(triples(relationships))


def consistent(*statements):
    options = arg_parser.parse_known_args()[0]  # apparently returns a tuple
    stats["statements"] += logic.count(statements)
    statements = [logic.compile(s) for s in statements]

    rels = relationships(statements)

    formula = and_(*(consistency(rels) + list(statements)))
    if options.tseytin:
        formula = formula.tseytin(aux)

    stats["size"] += formula.size()
    stats["degree"] = max(stats["degree"], formula.degree())
    return formula
