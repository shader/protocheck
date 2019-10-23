import pytest
from boolexpr import not_
from protocheck.bspl import *
from protocheck import precedence, logic


@pytest.fixture(scope="module")
def Auction():
    return load_file('samples/bspl/auction').protocols['Auction']


@pytest.fixture(scope="module")
def A(Auction):
    return Auction.roles['A']


@pytest.fixture(scope="module")
def B(Auction):
    return Auction.roles['B']


@pytest.fixture(scope="module")
def Bid(Auction):
    return Auction.messages['Bid']


@pytest.fixture(scope="module")
def WithReject():
    return load_file('samples/bspl/composition').protocols['With-Reject']


def test_keys(Bid, Auction):
    print(Auction.keys)
    assert [p for p in Auction.keys] == ["id"]
    # id explicitly declared key in P, but not message. Should still be considered a key
    print(Bid.keys)
    assert len({p for p in Bid.keys}) == 2


def test_parameter(Bid, Auction):
    assert len(Bid.parameters.values()) > 0
    p = Bid.parameters.get('id', None)
    assert p
    assert p.adornment


def test_params(Bid):
    assert len(Bid.ins) == 1
    assert "id" in Bid.ins

    assert len(Bid.outs) == 2
    assert "bidID" in Bid.outs
    assert "bid" in Bid.outs

    assert len(Bid.nils) == 1
    assert "done" in Bid.nils


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
    assert str(observe(A, Bid)) == 'A:Auction/Bid'


def test_transmission(Bid, A, B):
    assert logic.compile(Bid.transmission).equiv(
        or_(not_(observe(A, Bid)),
            sequential(observe(B, Bid),
                       observe(A, Bid))))


def test_reception(Bid, B):
    assert precedence.consistent(Bid.reception)


def test_role_messages(A):
    assert A.messages


def test_minimality(A, Auction):
    assert A.minimality
    print(A.minimality)
    assert consistent(A.minimality(Auction))


def test_enactable(Auction):
    assert Auction.enactability
    assert consistent(Auction.enactability)


def test_correct(Auction):
    c = Auction.correct
    assert c
    assert consistent(Auction.correct)


def test_maximal(Auction):
    assert Auction.maximal
    assert consistent(Auction.maximal)


def test_begin(Auction):
    assert Auction.begin
    assert consistent(Auction.begin)


def test_complete(Auction):
    print(Auction.complete)
    assert Auction.complete
    assert consistent(Auction.complete)


def test_is_enactable(Auction):
    assert Auction.is_enactable()


def test_protocol_dead_end(Auction):
    assert Auction.dead_end
    print(Auction.dead_end)
    o = consistent(Auction.dead_end)
    if o:
        print([k for k, v in o.items() if v])
    assert not o


def test_is_live(Auction):
    assert Auction.is_live()


def test_protocol_unsafe(Auction):
    o = consistent(Auction.unsafe)
    if o:
        print([k for k, v in o.items() if v == 1])
    assert not o


def test_protocol_safe(Auction):
    assert Auction.is_safe()


def test_protocol_is_atomic(Auction):
    assert Auction.is_atomic()


def test_protocol_cover(Auction):
    assert Auction.cover


def test_parameter_format(Bid):
    assert Bid.parameters['bidID'].format() == "out bidID key"


def test_message_format(Bid):
    assert Bid.format(
    ) == "B -> A: Bid[in id, out bidID key, out bid, nil done]"


def test_protocol_format(Auction, WithReject):
    assert Auction.format() == """Auction {
  roles A, B
  parameters out id key, out done
  private bidID, bid

  A -> B: Start[out id]
  B -> A: Bid[in id, out bidID key, out bid, nil done]
  A -> B: Stop[in id, out done]
}"""

    assert WithReject.format() == """With-Reject {
  roles C, S
  parameters out item key, out done

  Order(C, S, out item key, out done)
  S -> C: Reject[in item, out done]
}"""
