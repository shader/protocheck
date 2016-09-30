import pytest
from precedence.bspl import *
from precedence import precedence

@pytest.fixture(scope="module")
def Auction():
    with open('precedence/test/samples/bspl/auction') as file:
        return load(file.read())[0]

@pytest.fixture(scope="module")
def A(Auction):
    return Auction.roles['A']

@pytest.fixture(scope="module")
def B(Auction):
    return Auction.roles['B']

@pytest.fixture(scope="module")
def Bid(Auction):
    return Auction.messages['Bid']

def test_keys(Bid, Auction):
    assert [p.name for p in Auction.keys] == ["id"]
    #id explicitly declared key in P, but not message. Should still be considered a key
    assert len({p for p in Bid.keys}) == 2
    assert Auction.parameters['id'] in Bid.keys

def test_parameter(Bid, Auction):
    assert len(Bid.parameters.values()) > 0
    p = Bid.parameters.get('id', None)
    assert p
    assert p.adornment
    
def test_params(Bid):
    assert len(Bid.ins) == 1
    assert "id" in {p.name for p in Bid.ins}

    assert len(Bid.outs) == 2
    assert "bidID" in [p.name for p in Bid.outs]
    assert "bid" in [p.name for p in Bid.outs]

    assert len(Bid.nils) == 1
    assert "done" in {p.name for p in Bid.nils}

def test_msg_roles(Bid):
    assert Bid.sender.name == "B"
    assert Bid.recipient.name == "A"

def test_protocol_roles(Auction):
    assert len(Auction.roles.keys()) == 2
    assert Auction.roles['A'].name == "A"

def test_protocol_messages(Auction):
    assert len(Auction.messages) == 3
    assert Auction.messages.get('Bid')

def test_observe(Bid, A):
    assert str(observe(A, Bid)) == 'A:Bid'

def test_transmission(Bid, A, B):
    assert transmission(Bid, A, B).equiv(
        or_(not_(observe(B,Bid)),
           sequential(observe(A, Bid),
                      observe(B, Bid))))

def test_reception(Bid, B):
    assert precedence.consistent(reception(Bid, B)).sat()[0]

def test_role_ordering(A):
    assert A.ordering
    assert consistent(A.ordering)

def test_role_messages(A):
    assert A.messages

def test_minimality(A):
    assert A.minimality
    assert consistent(A.minimality)

def test_enactable(Auction):
    assert Auction.enactable
    assert consistent(Auction.enactable)

#@pytest.mark.skip(reason='Slow')
def test_correct(Auction):
    c = Auction.correct
    assert c
    assert consistent(Auction.correct).sat()[1]

#@pytest.mark.skip(reason='Slow')
def test_maximal(Auction):
    assert Auction.maximal
    assert consistent(Auction.maximal).sat()[1]

def test_begin(Auction):
    assert Auction.begin
    assert consistent(Auction.begin).sat()[1]

def test_complete(Auction):
    assert Auction.complete
    assert consistent(Auction.complete).sat()[1]

#@pytest.mark.skip(reason='Slow')
def test_is_enactable(Auction):
    assert Auction.is_enactable()

#@pytest.mark.skip(reason='Slow')
def test_protocol_dead_end(Auction):
    assert Auction.dead_end
    #print("complete: ", Auction.complete)
    #print("correct: ", Auction.correct)
    e = consistent(Auction.dead_end)
    print(e.size())
    o = e.sat()[1]
    if o:
        print([k for k,v in o.items() if v])
    assert not o

#@pytest.mark.skip(reason='Slow')
def test_is_live(Auction):
    assert Auction.is_live()

#@pytest.mark.skip(reason='Slow')
def test_protocol_unsafe(Auction):
    o = consistent(Auction.unsafe).sat()[1]
    if o:
        print([k for k,v in o.items() if v==1])
    assert not o

@pytest.mark.skip(reason='Slow')
def test_protocol_safe(Auction):
    assert Auction.is_safe()

def test_protocol_is_atomic(Auction):
    assert Auction.is_atomic()
