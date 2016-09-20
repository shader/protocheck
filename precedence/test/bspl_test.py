from precedence.bspl import *
from precedence import precedence

P = Protocol({
    "roles": [{
        "name": "A",
    },
    {
        "name": "B",
    }],
    "parameters": [
        {"adornment": "out", "name": "id", "key": "key"}
    ]
})

Bid = Message({
    "type": "message",
    "sender": "A",
    "recipient": "B",
    "name": "Bid",
    "parameters": [
        {
            "adornment": "in",
            "name": "id",
            "key": None,
        },
        {
            "adornment": "out",
            "name": "bid",
            "key": None,
        },
        {
            "adornment": "nil",
            "name": "done",
            "key": None
        }
    ]
}, protocol=P)

A = Role({
    "name": "A",
})
B = Role({
    "name": "B",
})

def test_keys():
    #id explicitly declared key in protocol, but not message. Should still be considered a key
    assert Bid.keys == ["id"]

def test_parames():
    assert len(Bid.ins) == 1
    assert Bid.ins[0]["name"] == "id"

    assert len(Bid.outs) == 1
    assert Bid.outs[0]["name"] == "bid"

    assert len(Bid.nils) == 1
    assert Bid.nils[0]["name"] == "done"

def test_msg_roles():
    assert Bid.sender == "A"
    assert Bid.recipient == "B"

def test_protocol_roles():
    assert len(P.roles.keys()) == 2
    assert P.roles['A'].name == "A"

def test_observe():
    assert str(observe(A, Bid)) == 'A:Bid'

def test_transmission():
    assert transmission(Bid, A, B).equivalent(
        Or(Not(observe(B,Bid)),
           sequential(observe(A, Bid),
                      observe(B, Bid))))

def test_reception():
    #assert reception(Bid, B) is None
    assert precedence.consistent(reception(Bid, B)).satisfy_one()
