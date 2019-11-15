import pytest
from ttictoc import TicToc
from statistics import median
from protocheck.refinement import *


def perf_test(objects, properties):
    t = TicToc()
    for obj in objects:
        for name, fn in properties.items():
            times = []
            for x in range(10 + 1):
                t.tic()
                fn(obj)
                t.toc()
                if x > 0:  # burn in once
                    times.append(t.elapsed * 1000)  # use milliseconds
            mean = sum(times) / len(times)
            print(
                f"{obj.name}, {name}, {int(min(times))}, {int(mean)}, {int(max(times))}, {times}")


@pytest.fixture(scope="module")
def Concurrent():
    return load_file('samples/bspl/performance/concurrent.bspl')


@pytest.fixture(scope="module")
def Linear():
    return load_file('samples/bspl/performance/linear.bspl')


@pytest.fixture(scope="module")
def OneIndependent():
    return load_file('samples/bspl/performance/one-independent.bspl')


@pytest.fixture(scope="module")
def PurchaseComposition():
    return load_file('samples/bspl/refinement/purchase-composition.bspl')


# def test_linear(Linear):
#     t = TicToc()
#     print("Linear: ")
#     print("protocol,paths,min,mean,max")
#     for protocol in Linear.protocols.values():
#         times = []
#         paths = []
#         U = UoD.from_protocol(protocol)
#         for x in range(10):
#             t.tic()
#             paths = all_paths(U)
#             t.toc()
#             times.append(t.elapsed)
#         print(f"{protocol.name}, {len(paths)}, {min(times):0.4f}, {sum(times) / len(times):0.4f}, {max(times):0.4f}")


# def test_concurrent_paths(Concurrent):
#     t = TicToc()
#     print("protocol,paths,min,mean,max")
#     for protocol in Concurrent.protocols.values():
#         times = []
#         paths = None
#         for x in range(10):
#             t.tic()
#             paths = all_paths(UoD.from_protocol(protocol))
#             t.toc()
#             times.append(t.elapsed)
#         print(f"{protocol.name}, {len(paths)}, {min(times):0.4f}, {sum(times) / len(times):0.4f}, {max(times):0.4f}")


# def test_concurrent_refinement(Concurrent):
#     t = TicToc()
#     print("protocol,paths,min,mean,max")
#     for protocol in Concurrent.protocols.values():
#         times = []
#         paths = None
#         for x in range(10):
#             t.tic()
#             paths = refines(UoD(), protocol.public_parameters,
#                             protocol, protocol)
#             t.toc()
#             times.append(t.elapsed)
#         print(f"{protocol.name}, {len(paths)}, {min(times):0.4f}, {sum(times) / len(times):0.4f}, {max(times):0.4f}")


# def test_one_independent(OneIndependent):
#     t = TicToc()
#     print("protocol,paths,min,mean,max")
#     for protocol in OneIndependent.protocols.values():
#         times = []
#         paths = 0
#         for x in range(10):
#             t.tic()
#             paths = all_paths(UoD.from_protocol(protocol))
#             t.toc()
#             times.append(t.elapsed)
#         print(f"{protocol.name}, {len(paths)}, {min(times):0.4f}, {sum(times) / len(times):0.4f}, {max(times):0.4f}")


def test_refinement_performance(PurchaseComposition):
    t = TicToc()
    print("Refinement: ")
    print("Protocol, Min, Avg, Max")
    Ps = ['Either-Starts', 'Lookup-Prices', 'Flexible-Payment']
    Qs = ['Buyer-Starts', 'Single-Lookup', 'Pay-First']
    for i, name in enumerate(Ps):
        P = PurchaseComposition.protocols[Ps[i]]
        Q = PurchaseComposition.protocols[Qs[i]]
        times = []
        for x in range(10):
            t.tic()
            refines(UoD(), P.public_parameters, Q, P)
            t.toc()
            times.append(t.elapsed * 1000)
        avg = sum(times) / len(times)
        print(f"{P.name}, {int(min(times))}, {int(avg)}, {int(max(times))}, {times}")


def test_sat_composition_performance(PurchaseComposition):
    t = TicToc()
    print("SAT (composition): ")
    print('Protocol, Property, Min, Mean, Max, Times')
    properties = {
        "Liveness": lambda P: P.is_live(),
        "Safety": lambda P: P.is_safe()
    }
    perf_test([PurchaseComposition.protocols['Refined-Commerce']], properties)


def test_sat_subprotocol_performance(PurchaseComposition):
    t = TicToc()
    print("SAT (components): ")
    print('Protocol, Property, Min, Mean, Max')

    for P in PurchaseComposition.protocols.values():
        if 'Commerce' in P.name:
            continue
        properties = {
            "Enactability": P.is_enactable,
            "Liveness": P.is_live,
            "Safety": P.is_safe
        }
        for name, fn in properties.items():
            times = []
            for x in range(10):
                t.tic()
                fn()
                t.toc()
                print(t.elapsed)
                times.append(t.elapsed * 1000)  # use milliseconds
            mean = sum(times) / len(times)
            print(
                f"{P.name}, {name}, {int(min(times))}, {int(mean)}, {int(max(times))}")


def test_single_sub_performance(PurchaseComposition):
    t = TicToc()
    print("SAT (single sub): ")
    print('Protocol, Property, Min, Mean, Max, Times')

    specs = ['sub-buyer-starts.bspl',
             'sub-pay-first.bspl',
             'sub-single-lookup.bspl']

    for s in specs:
        P = load_file('samples/bspl/performance/' +
                      s).protocols['Refined-Commerce']
        properties = {
            "Liveness": P.is_live,
            "Safety": P.is_safe
        }
        for name, fn in properties.items():
            times = []
            for x in range(10 + 1):
                t.tic()
                fn()
                t.toc()
                if x > 0:  # burn in once
                    times.append(t.elapsed * 1000)  # use milliseconds
            mean = sum(times) / len(times)
            print(
                f"{s}, {name}, {int(min(times))}, {int(mean)}, {int(max(times))}, {times}")


def test_single_sub_path_performance(PurchaseComposition):
    print("SAT (single sub): ")
    print('Protocol, Property, Min, Mean, Max, Times')

    specs = [  # 'sub-buyer-starts.bspl',
        #'sub-pay-first.bspl',
        #'sub-single-lookup.bspl',
        'purchase-composition.bspl']

    for s in specs:
        P = load_file('samples/bspl/performance/' +
                      s).protocols['Refined-Commerce']
        properties = {
            "Liveness": path_liveness,
            "Safety": path_safety
        }
        perf_test([P], properties)


def test_netbill_refinement(PurchaseComposition):
    print("NetBill refinement: ")
    print('Protocol, Property, Min, Mean, Max, Times')

    spec = load_file('samples/bspl/refinement/netbill.bspl')
    P = spec.protocols['NetBill-Bliss']
    Q = spec.protocols['Original-NetBill']
    properties = {
        "Refinement": lambda q: refines(UoD(), P.public_parameters, q, P),
        "Liveness": lambda p: p.is_live(),
        "Safety": lambda p: p.is_safe(),
        "Path-Liveness": path_liveness,
        "Path-Safety": path_safety,
    }
    perf_test([Q], properties)


def test_CreateLabOrder_refinement(PurchaseComposition):
    print("CreateLabOrder refinement: ")
    print('Protocol, Property, Min, Mean, Max, Times')

    spec = load_file('samples/bspl/refinement/lab-order-refinement.bspl')
    P = spec.protocols['CreateOrder']
    Q = spec.protocols['CreateOrder2']
    properties = {
        "Refinement": lambda q: refines(UoD(), P.public_parameters, q, P),
        "Liveness": lambda p: p.is_live(),
        "Safety": lambda p: p.is_safe(),
        "Path-Liveness": path_liveness,
        "Path-Safety": path_safety,
    }
    perf_test([Q], properties)


def run_all():
    test_linear(load_file('samples/bspl/performance/linear.bspl'))
    test_concurrent(load_file('samples/bspl/performance/concurrent.bspl'))
    test_one_independent(
        load_file('samples/bspl/performance/one-independent.bspl'))
