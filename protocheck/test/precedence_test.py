import pytest
from boolexpr import and_, not_, impl
from protocheck.precedence import (
    transitivity, relationships, var,
    occurrence, simultaneous, sequential,
    timeline,
    invert,
    normalize,
    pivot,
    antipivot,
    align,
    outer,
    match,
    triples
)


def test_occurrence():
    occ = occurrence(relationships([simultaneous('a', 'b')]))
    print('occurrence: ', occ)
    formula = and_(simultaneous('a', 'b'), not_(var('a')), *occ)
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
    formula = and_(var('a'), var('b'), *(t + statements))
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


def test_pivot():
    assert pivot((1, 2), (2, 3)) == 2


def test_antipivot():
    assert antipivot((1, 2), (2, 3)) == 1


def test_align():
    assert align((1, 2), (2, 3)) == ((1, 2), (2, 3))
    assert align((1, 2), (3, 2)) == ((1, 2), (2, 3))


def test_outer():
    assert outer((1, 2), (2, 3)) == (1, 3)


def test_match():
    a = (1, 2)
    rels = {'<'}
    assert rels == match(a, a, rels)
    assert {'>'} == match(a, (2, 1), rels)


def test_triples():
    # shouldn't generate transitivity since the bridge clause doesn't exist
    assert not triples(relationships([sequential('a', 'b'),
                                      sequential('b', 'c')]))
    # this one should though
    assert triples(relationships([sequential('a', 'b'),
                                  sequential('b', 'c'),
                                  sequential('a', 'c')]))


def test_transitivity():
    def trans(s):
        return transitivity(triples(relationships(s)))

    statements = [sequential('a', 'b'),
                  sequential('b', 'c'),
                  sequential('d', 'e')]
    assert [] == trans(statements)

    statements += sequential('a', 'c')
    assert trans(statements)[0].equiv(
        impl(and_(var("a<b"), var("b<c")), var("a<c")))
