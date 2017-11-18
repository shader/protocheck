"""
Logic operations for combining objects that represent named statements, to improve readability.

Named statements are represented as name/statement pairs in a dict.
Because conjunction is more common, it is represented my merging dicts.
Disjunction is represented by a list instead.

E.x.:
>>> a = Name(a, "A")
{"A": a}
>>> b = Name(b, "B")
{"B": b}
>>> And(a,b)
{"A": a, "B": b}
>>> Or(a,b)
[{"A":a}, {"B":b}]
"""

import boolexpr as bx
from boolexpr import *
from itertools import combinations, permutations, chain

def merge(*dicts):
    """
    Given any number of dicts, shallow copy and merge into a new dict,
    precedence goes to key value pairs in latter dicts.
    """
    result = {}
    for dictionary in dicts:
        result.update(dictionary)
    return result

def Name(statement, name):
    return {name: statement}

def And(*statements):
    o = {}
    for s in statements:
        o = merge(o, s)
    return o

def Or(*statements):
    return statements

def count(statements):
    if type(statements) is list or type(statements) is tuple:
        # disjunction
        return sum(count(s) for s in statements)
    elif type(statements) is dict:
        # conjunction
        return sum(count(s) for s in statements.values())
    else:
        # atomic statement
        return 1

def compile(statements):
    if type(statements) is list or type(statements) is tuple:
        # disjunction
        return or_s(*[compile(s) for s in statements])
    elif type(statements) is dict:
        # conjunction
        return and_s(*[compile(s) for s in statements.values()])
    else:
        # atomic statement
        return statements

def named(arg):
    def wrap(fn, name=arg):
        """Wrapper for functions that return logic statements, to track where
they came from"""
        def wrapped(*args, **kwds):
            n = name or "-".join([a.name for a in args] + [fn.__name__])
            return Name(fn(*args, **kwds), n)
        return wrapped

    if type(arg) is str:
        return wrap
    else:
        return wrap(arg, None)
