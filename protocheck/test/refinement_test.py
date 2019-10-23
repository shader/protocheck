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


@pytest.fixture(scope="module")
def ConcurrencyElimination():
    return load_file('samples/bspl/refinement/concurrency-elimination.bspl')


@pytest.fixture(scope="module")
def Flexible(ConcurrencyElimination):
    return ConcurrencyElimination.protocols["Flexible-Purchase"]


@pytest.fixture(scope="module")
def ShipFirst(ConcurrencyElimination):
    return ConcurrencyElimination.protocols["Ship-First"]


@pytest.fixture(scope="module")
def KeyReduction():
    return load_file('samples/bspl/refinement/key-reduction.bspl')


def test_known_empty(P):
    assert known(empty_path(), {}, P.roles['A']) == set()


def test_known_simple(P):
    print("test keys: ", P.messages['test'].keys)
    assert known([Instance(P.messages['test'], 0)],
                 P.messages['test'].keys, P.roles['A']) == {'data', 'id'}


def test_viable(P, Flexible):
    test = P.messages['test']
    assert viable(empty_path(), test)
    assert not viable([Instance(test, 0)], test)

    rfq = Flexible.messages['rfq']
    print("S knows: ", known([Instance(rfq, 0)],
                             rfq.keys, Flexible.roles['S']))
    assert rfq.keys == Flexible.messages['pay'].keys
    assert viable([Instance(rfq, 0)], Flexible.messages["pay"])


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
    assert sources([Instance(P.messages['test'])], 'id') == {'A'}


def test_subsumes(P, Q, KeyReduction):
    U = UoD.from_protocol(P)
    params = {'id', 'data'}
    assert subsumes(UoD(), set(), empty_path(), empty_path())
    assert subsumes(U, params, empty_path(), empty_path())

    assert subsumes(U, params, [Instance(Q.messages['test'], 0)], [
                    Instance(P.messages['test'], 0)])

    assert not subsumes(U, params, empty_path(), [
        Instance(P.messages['test'])])

    assert not subsumes(
        U, params, [Instance(P.messages['test'])], empty_path())

    KeyP = KeyReduction.protocols['P']
    KeyQ = KeyReduction.protocols['Q']
    print(known([Instance(KeyQ.messages['test'], 0)],
                KeyQ.messages['test'].keys, KeyQ.roles['A']))
    print(known([Instance(KeyP.messages['test'], 0)],
                KeyQ.messages['test'].keys, KeyQ.roles['A']))
    assert subsumes(
        UoD.from_protocol(KeyP),
        KeyP.keys,
        [Instance(KeyQ.messages['test'], 0)],
        [Instance(KeyP.messages['test'], 0)]
    )


def test_max_paths(P):
    U = UoD.from_protocol(P)

    assert max_paths(U) == [[Instance(P.messages['test'], 0)]]


def test_all_paths(P, Flexible):
    assert all_paths(UoD.from_protocol(P)) == [empty_path(), [
        Instance(P.messages['test'], 0)]]

    assert len(all_paths(UoD.from_protocol(Flexible))) > 2


def test_refines(Q, P):
    U = UoD()
    params = {'id', 'data'}

    assert refines(U, P.public_parameters.keys(), Q, P) == {"ok": True}


def test_concurrency_elimination(Flexible, ShipFirst):
    # print(all_paths(UoD.from_protocol(Flexible)))
    # print(all_paths(UoD.from_protocol(ShipFirst)))
    assert refines(UoD(), Flexible.public_parameters.keys(),
                   ShipFirst, Flexible) == {"ok": True}

    assert refines(UoD(), Flexible.public_parameters.keys(),
                   Flexible, ShipFirst) != {"ok": True}


def test_initiation_reduction():
    spec = load_file('samples/bspl/refinement/initiation-reduction.bspl')
    EitherStarts = spec.protocols["Either-Starts"]
    BuyerStarts = spec.protocols["Buyer-Starts"]
    assert refines(UoD(), EitherStarts.public_parameters.keys(),
                   BuyerStarts, EitherStarts) == {"ok": True}

    assert refines(UoD(), BuyerStarts.public_parameters.keys(),
                   EitherStarts, BuyerStarts) != {"ok": True}


def test_polymorphism():
    spec = load_file('samples/bspl/refinement/polymorphism.bspl')
    RFQ = spec.protocols["RFQ"]
    RefinedRFQ = spec.protocols["Refined-RFQ"]
    assert refines(UoD(), RFQ.public_parameters.keys(),
                   RefinedRFQ, RFQ) == \
        {"ok": False,
         'path': [Instance(RefinedRFQ.messages['Introduction'], 0)],
         'reason': 'Refined-RFQ has path that does not subsume any path in RFQ'}

    assert refines(UoD(), RefinedRFQ.public_parameters.keys(),
                   RFQ, RefinedRFQ) != {"ok": True}


def test_dependent():
    spec = load_file('samples/bspl/refinement/basic-dependent.bspl')
    P = spec.protocols["P"]
    Q = spec.protocols["Q"]
    assert refines(UoD(), P.public_parameters.keys(),
                   Q, P) == {"ok": True}

    assert refines(UoD(), Q.public_parameters.keys(),
                   P, Q) == {"ok": True}


def test_key_reduction():
    spec = load_file('samples/bspl/refinement/key-reduction.bspl')
    P = spec.protocols["P"]
    p_test = P.messages['test']
    Q = spec.protocols["Q"]
    q_test = Q.messages['test']
    print("P test keys: ", p_test.keys)
    print("Q test keys: ", q_test.keys)

    assert refines(UoD(), P.public_parameters.keys(),
                   Q, P) == {"ok": True}

    assert refines(UoD(), Q.public_parameters.keys(),
                   P, Q) != {"ok": True}
