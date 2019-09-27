import pytest
from protocheck.refinement import *


@pytest.fixture(scope="module")
def BasicRefinement():
    return load_file('samples/bspl/refinement/basic.bspl')


@pytest.fixture(scope="module")
def P(BasicRefinement):
    return BasicRefinement.protocols['P']


@pytest.fixture(scope="module")
def Q(BasicRefinement):
    return BasicRefinement.protocols['Q']


def test_known_empty(P):
    assert known(empty_path(), P.roles['A']) == set()


def test_viable(P):
    test = P.messages['test']
    assert viable(empty_path(), test)
    assert not viable([Instance(test, 0)], test)


def test_branches(P):
    u = UoD.from_protocol(P)
    assert branches(u, empty_path()) == {
        Instance(P.messages['test'], float('inf'))}


def test_unreceived(P):
    path = [Instance(P.messages['test'], float('inf'))]
    assert len(unreceived(path)) == 1


def test_extensions(P):
    u = UoD.from_protocol(P)
    p1 = [Instance(P.messages['test'], float('inf'))]
    assert extensions(u, empty_path()) == [p1]
    assert extensions(u, p1) == [
        [Instance(P.messages['test'], 0)]]


def test_sources(P):
    assert sources(empty_path(), P.parameters['id']) == set()
    assert sources([Instance(P.messages['test'])], 'id') == {
        P.roles['A']}


def test_subsumes(P):
    U = UoD.from_protocol(P)
    params = {'id', 'data'}
    assert subsumes(U, params, empty_path(), empty_path())

    assert subsumes(U, params, [Instance(P.messages['test'])], [
                    Instance(P.messages['test'])])

    assert not subsumes(U, params, empty_path(), [
        Instance(P.messages['test'])])

    assert not subsumes(
        U, params, [Instance(P.messages['test'])], empty_path())


def test_max_paths(P):
    U = UoD.from_protocol(P)

    assert max_paths(U) == [[Instance(P.messages['test'], 0)]]


def test_all_paths(P):
    U = UoD.from_protocol(P)

    assert all_paths(U) == [empty_path(), [
        Instance(P.messages['test'], 0)]]


def test_refines(Q, P):
    U = UoD.from_protocol(Q)
    params = {'id', 'data'}

    assert refines(U, params, Q, P)
