import pytest
from ttictoc import TicToc
from protocheck.refinement import *


@pytest.fixture(scope="module")
def Concurrent():
    return load_file('samples/bspl/performance/concurrent.bspl')


@pytest.fixture(scope="module")
def Linear():
    return load_file('samples/bspl/performance/linear.bspl')


@pytest.fixture(scope="module")
def OneIndependent():
    return load_file('samples/bspl/performance/one-independent.bspl')


def test_linear(Linear):
    t = TicToc()
    for protocol in Linear.protocols.values():
        t.tic()
        U = UoD.from_protocol(protocol)
        paths = all_paths(U)
        t.toc()
        print("Paths in {}: {}".format(protocol.name, len(paths)))
        print("Elapsed time: {}".format(t.elapsed))


def test_concurrent(Concurrent):
    t = TicToc()
    for protocol in Concurrent.protocols.values():
        t.tic()
        paths = all_paths(UoD.from_protocol(protocol))
        t.toc()
        print("Paths in {}: {}".format(protocol.name, len(paths)))
        print("Elapsed time: {}".format(t.elapsed))


def test_one_independent(OneIndependent):
    t = TicToc()
    for protocol in OneIndependent.protocols.values():
        t.tic()
        paths = all_paths(UoD.from_protocol(protocol))
        t.toc()
        print("Paths in {}: {}".format(protocol.name, len(paths)))
        print("Elapsed time: {}".format(t.elapsed))


def run_all():
    test_linear(load_file('samples/bspl/performance/linear.bspl'))
    test_concurrent(load_file('samples/bspl/performance/concurrent.bspl'))
    test_one_independent(
        load_file('samples/bspl/performance/one-independent.bspl'))
