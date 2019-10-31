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


@pytest.fixture(scope="module")
def AddIntermediary():
    return load_file('samples/bspl/refinement/add-intermediary.bspl')


@pytest.fixture(scope="module")
def AllIn():
    return load_file('samples/bspl/refinement/all-in.bspl')


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


def test_viable_all_in(AllIn):
    P = AllIn.protocols['P']
    test = P.messages['test']

    assert not viable(empty_path(), test)
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
    p1 = (Instance(P.messages['test'], float('inf')), )
    assert extensions(u, empty_path()) == {p1}
    assert extensions(u, p1) == {(Instance(P.messages['test'], 0), )}


def test_sources(P):
    assert sources(empty_path(), P.parameters['id']) == set()
    assert sources([Instance(P.messages['test'])], 'id') == {'A'}


def test_subsumes(P, Q):
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


def test_subsumes_initiation_reduction():
    spec = load_file('samples/bspl/refinement/initiation-reduction.bspl')
    EitherStarts = spec.protocols["Either-Starts"]
    BuyerStarts = spec.protocols["Buyer-Starts"]
    assert subsumes(UoD.from_protocol(EitherStarts),
                    EitherStarts.public_parameters.keys(),
                    [Instance(BuyerStarts.messages['rfq'], 0)],
                    [Instance(EitherStarts.messages['rfq'], 0)],
                    verbose=True)


def test_subsumes_key_reduction(KeyReduction):
    KeyP = KeyReduction.protocols['P']
    KeyQ = KeyReduction.protocols['Q']
    path_q = (Instance(KeyQ.messages['test'], 0), )
    path_p = (Instance(KeyP.messages['test'], 0), )
    print(known(path_q,
                KeyQ.messages['test'].keys, KeyQ.roles['A']))
    print(known(path_p,
                KeyQ.messages['test'].keys, KeyQ.roles['A']))
    assert subsumes(
        UoD.from_protocol(KeyP),
        KeyP.public_parameters.keys(),
        path_q,
        path_p,
        verbose=True)


def test_max_paths(P):
    U = UoD.from_protocol(P)

    assert max_paths(U) == [(Instance(P.messages['test'], 0), )]


def test_all_paths(P, Flexible):
    assert all_paths(UoD.from_protocol(P)) == {empty_path(), (
        Instance(P.messages['test'], 0), )}

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
    assert refines(UoD(),
                   EitherStarts.public_parameters.keys(),
                   BuyerStarts,
                   EitherStarts,
                   verbose=True) == {"ok": True}

    assert refines(UoD(), BuyerStarts.public_parameters.keys(),
                   EitherStarts, BuyerStarts,
                   verbose=True) != {"ok": True}


def test_message_split():
    spec = load_file('samples/bspl/refinement/message-split.bspl')
    RFQ = spec.protocols["RFQ"]
    RefinedRFQ = spec.protocols["Refined-RFQ"]
    assert refines(UoD(), RFQ.public_parameters.keys(),
                   RefinedRFQ, RFQ)["ok"]

    # {"ok": False,
    #  'path': (Instance(RefinedRFQ.messages['Introduction'], 0),),
    #  'reason': 'Refined-RFQ has path that does not subsume any path in RFQ'}

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


def test_polymorphism_reduction():
    spec = load_file('samples/bspl/refinement/polymorphism.bspl')
    P = spec.protocols["Polymorphic-RFQ"]
    Q = spec.protocols["RFQ"]
    assert refines(UoD(), P.public_parameters.keys(),
                   Q, P) == {"ok": True}

    assert refines(UoD(), Q.public_parameters.keys(),
                   P, Q)["ok"] == False


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


def test_all_in():
    spec = load_file('samples/bspl/refinement/all-in.bspl')
    P = spec.protocols["P"]
    p_test = P.messages['test']
    Q = spec.protocols["Q"]
    q_test = Q.messages['test']

    assert refines(UoD(), P.public_parameters.keys(),
                   Q, P) == {"ok": True}

    assert refines(UoD(), Q.public_parameters.keys(),
                   P, Q) == {"ok": True}


def test_add_intermediary(AddIntermediary):
    P = AddIntermediary.protocols["Simple-Purchase"]
    Q = AddIntermediary.protocols["Escrow-Purchase"]

    assert refines(UoD(), P.public_parameters.keys(),
                   Q, P) == {"ok": True}

    assert refines(UoD(), Q.public_parameters.keys(),
                   P, Q) != {"ok": True}
