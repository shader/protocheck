from precedence.spl import *
from precedence import precedence

Bid = Message({
    "type": "message",
    "sender": "B",
    "recipients": "P",
    "name": "Bid",
    "key": [
        {
            "name": "id",
            "adornment": None,
            "op": None,
            "expr": None
        },
        {
            "adornment": "out",
            "name": "bidID",
            "op": None,
            "expr": None
        },
        {
            "adornment": "out",
            "name": "bidder",
            "op": "\u2208",
            "expr": [
                "B"
            ]
        }
    ],
    "data": [
        {
            "adornment": "out",
            "name": "bid",
            "op": None,
            "expr": None
        },
        {
            "adornment": "nil",
            "name": "done",
            "op": None,
            "expr": None
        }
    ]
})

A = Role({
    "name": "A",
    "set_": None,
    "op": None,
    "expr": None
})

B = Role({
    "set_": "set",
    "name": "B",
    "op": None,
    "expr": None
})

def test_observe():
    assert str(observe(A, Bid)) == 'A:Bid'

def test_transmission():
    assert transmission(Bid, A, B).equivalent(Or(Not(observe(B,Bid)), sequential(observe(A, Bid), observe(B, Bid))))

def test_reception():
    #assert reception(Bid, B) is None
    assert precedence.consistent(reception(Bid, B)).satisfy_one()
