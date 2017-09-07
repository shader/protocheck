import pytest
from boolexpr import and_, not_
from protocheck.precedence import (
    transitivity, relationships, var,
    occurrence, simultaneous, sequential, extract_events
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
