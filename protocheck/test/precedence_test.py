import pytest
from protocheck.precedence import *

def test_occurrence():
    occ = occurrence(*extract_events(simultaneous('a', 'b')))
    print('occurrence: ', occ)
    formula = and_(occ, simultaneous('a', 'b'), not_(var('a')))
    print('formula: ', formula)
    s = formula.sat()[1]
    if s:
        print('solution: ', [k for k,v in s.items() if v])
    assert not s

