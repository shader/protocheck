import pytest
from precedence.bspl import *
from precedence import precedence

@pytest.fixture
def Auction():
    with open('precedence/test/samples/bspl/auction') as file:
        return Protocol.load(file.read())

@pytest.fixture
def Basic():
    with open('precedence/test/samples/bspl/basic') as file:
        return Protocol.load(file.read())

@pytest.fixture
def A():
    return Role({
        "name": "A",
    })

@pytest.fixture
def B():
    return Role({
        "name": "B",
    })

@pytest.fixture
def Bid(Auction):
    return Auction.messages['Bid']

def test_keys(Bid, Basic):
    assert Basic.keys == ["id"]
    #id explicitly declared key in P, but not message. Should still be considered a key
    assert len(Bid.keys) == 2
    assert 'bidID' in Bid.keys
    assert 'id' in Bid.keys

def test_params(Bid):
    assert len(Bid.ins) == 1
    assert Bid.ins[0]["name"] == "id"

    assert len(Bid.outs) == 2
    assert Bid.outs[0]["name"] == "bidID"
    assert Bid.outs[1]["name"] == "bid"

    assert len(Bid.nils) == 1
    assert Bid.nils[0]["name"] == "done"

def test_msg_roles(Bid):
    assert Bid.sender == "B"
    assert Bid.recipient == "A"

def test_protocol_roles(Basic):
    assert len(Basic.roles.keys()) == 2
    assert Basic.roles['A'].name == "A"

def test_protocol_messages(Basic):
    assert len(Basic.messages) == 1
    assert Basic.messages.get('test')

def test_observe(Bid, A):
    assert str(observe(A, Bid)) == 'A:Bid'

def test_transmission(Bid, A, B):
    assert transmission(Bid, A, B).equivalent(
        Or(Not(observe(B,Bid)),
           sequential(observe(A, Bid),
                      observe(B, Bid))))

def test_reception(Bid, B):
    #assert reception(Bid, B) is None
    assert precedence.consistent(reception(Bid, B)).satisfy_one()
