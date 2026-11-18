from fractions import Fraction
from itertools import product, combinations
from collections import Counter

def intent(latency, correct, fallback):
    return (latency <= 10 and correct) or fallback

def rate(xs):
    return Fraction(sum(xs), len(xs)) if xs else None

contexts = list(product([False, True], repeat=2))
root_changes = [intent(8,c,f) != intent(12,c,f) for c,f in contexts]
assert rate(root_changes) == Fraction(1,4)
assert rate([]) is None  # empty catalogue is undefined
assert rate([True]*4) == 1

def mobius(values):
    result = []
    for mask in range(len(values)):
        subsets = [s for s in range(len(values)) if s & mask == s]
        result.append(sum((-1)**(mask.bit_count()-s.bit_count()) * values[s] for s in subsets))
    return result

def reconstructed(coeff):
    return [sum(coeff[s] for s in range(len(coeff)) if s & mask == s) for mask in range(len(coeff))]
for vals, expected in [([0,0,0,1],[0,0,0,1]),([0,1,1,1],[0,1,1,-1])]:
    coeff = mobius(vals)
    assert coeff == expected
    assert reconstructed(coeff) == vals

# State = latency, correctness, fallback, auxiliary setting.
rows = [((8,True,False,0),(9,True,False,0)),
        ((8,True,False,0),(12,True,False,0)),
        ((8,True,False,0),(8,False,False,0)),
        ((8,True,False,0),(8,True,False,1))]
table = Counter((a[0]!=b[0], intent(*a[:3])!=intent(*b[:3])) for a,b in rows)
assert table == Counter({(False,False):1,(False,True):1,(True,False):1,(True,True):1})
for a,b in rows:
    old, new = int(intent(*a[:3])), int(intent(*b[:3]))
    bridge = int(intent(a[0],*b[1:3]))
    assert new-old == (new-bridge)+(bridge-old)

receipts = [(i,x) for i,x in enumerate([True,True,True,False,False])]
def disagreement(deliveries):
    unique = {}
    for key,value in deliveries:
        assert key not in unique or unique[key] == value
        unique[key] = value
    values = list(unique.values())
    pairs = list(combinations(values,2))
    return rate([a!=b for a,b in pairs])
assert disagreement(receipts) == Fraction(3,5)
assert disagreement(receipts+receipts) == Fraction(3,5)
assert disagreement(list(reversed(receipts))) == Fraction(3,5)
assert disagreement(receipts[:1]) is None
assert rate([not v for _,v in receipts]) == Fraction(2,5)
print('PASS: direct pivotality 1/4; AND/OR interaction reconstruction; mutation partition; bridge decomposition; repetition disagreement 6/10; deduplication/permutation/empty scope.')
