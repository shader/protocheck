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
    triples,
    consistent,
    ordered
)


def test_ordered():
    assert not (ordered('a', 'b')
                & var('a')
                & var('b')
                & ~sequential('a', 'b')
                & ~sequential('b', 'a')).sat()[1]


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
    assert len(triples(relationships([sequential('a', 'b'),
                                      sequential('b', 'c')])).items()) == 1

    assert len(triples(relationships([sequential('a', 'b'),
                                      sequential('b', 'c'),
                                      sequential('c', 'd')])).items()) == 2


def test_transitivity():
    def trans(s):
        return transitivity(triples(relationships(s)))

    statements = [sequential('a', 'b'),
                  sequential('b', 'c'),
                  sequential('d', 'e')]
    assert len(trans(statements)) == 1

    statements += sequential('a', 'c')
    assert trans(statements)[0].equiv(
        impl(and_(var("a<b"), var("b<c")), var("a<c")))


def to_char(i):
    return bytes([i+b'a'[0]]).decode()


def chain(n):
    clauses = []
    for i in range(n):
        clauses.append(sequential(to_char(i), to_char(i+1)))
    return clauses


def test_consistent():
    # check basic consistency
    assert consistent(var('a'), var('b'), sequential('a', 'b'))

    # see how long a causal loop can be before transitivity stops working
    for i in range(1, 5):
        clauses = [sequential(to_char(i), 'a')] + chain(i)
        assert not consistent(and_(*clauses))


def test_exhaustive_consistent():
    # check basic consistency
    assert consistent(var('a'), var('b'), sequential('a', 'b'))

    # see how long a causal loop can be before transitivity stops working
    for i in range(1, 5):
        clauses = [sequential(to_char(i), 'a')] + chain(i)
        assert not consistent(and_(*clauses), exhaustive=True)
