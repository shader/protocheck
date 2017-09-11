import pytest
from boolexpr import and_, not_
from protocheck.precedence import (
    transitivity, relationships, var,
    occurrence, simultaneous, sequential, extract_events
    timeline,
    invert,
    normalize,
)


def test_occurrence():
    occ = occurrence(relationships([simultaneous('a', 'b')]))
    print('occurrence: ', occ)
    formula = and_(occ, simultaneous('a', 'b'), not_(var('a')))
    print('formula: ', formula)
    s = formula.sat()[1]
    if s:
        print('solution: ', [k for k, v in s.items() if v])
    assert not s


def test_relationships():
    statements = [simultaneous('a', 'b'), sequential('a', 'b')]
    rs = relationships(statements)
    assert ('a', 'b') in rs and len(rs[('a', 'b')]) == 2


def test_timeline():
    statements = [simultaneous('a', 'b'), sequential('b', 'a')]
    t = timeline(relationships(statements))
    print('timeline: ', t)
    formula = and_(t, var('a'), var('b'), *statements)
    print('formula: ', formula)
    s = formula.sat()[1]
    if s:
        print('solution: ', [k for k, v in s.items() if v])
    assert not s


def test_invert():
    assert invert({"*", ">"}) == {"*", "<"}


def test_normalize():
    assert normalize((1, 2), {"*", ">"}) == ((1, 2), {"*", ">"})
    assert normalize((2, 1), {"*", ">"}) == ((1, 2), {"*", "<"})
