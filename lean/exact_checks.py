#!/usr/bin/env python3
"""Independent exact arithmetic and finite stress checks; standard library only.

This is not a proof of geometric estimates. Lean files give the separately
kernel-checked theorems. Run: python3 exact_checks.py
"""
from fractions import Fraction as F
from itertools import product
from decimal import Decimal, localcontext
import json

checks = []
def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)

class Poly:
    """Sparse Laurent polynomials over Q, variables named in a fixed tuple."""
    names = ('a', 'b', 'c', 'u', 'm', 'd', 'dp', 'p', 'q', 'e', 'k')
    zero = (0,) * len(names)
    def __init__(self, terms):
        if isinstance(terms, (int, F)):
            terms = {self.zero: F(terms)}
        self.terms = {k: F(v) for k, v in terms.items() if v}
    @classmethod
    def var(cls, name, exponent=1):
        p = list(cls.zero); p[cls.names.index(name)] = exponent
        return cls({tuple(p): F(1)})
    def __add__(self, rhs):
        rhs = rhs if isinstance(rhs, Poly) else Poly(rhs)
        out = dict(self.terms)
        for p, c in rhs.terms.items(): out[p] = out.get(p, F(0)) + c
        return Poly(out)
    __radd__ = __add__
    def __neg__(self): return Poly({p: -c for p, c in self.terms.items()})
    def __sub__(self, rhs): return self + -as_poly(rhs)
    def __rsub__(self, rhs): return as_poly(rhs) + -self
    def __mul__(self, rhs):
        rhs = as_poly(rhs); out = {}
        for p, c in self.terms.items():
            for q, d in rhs.terms.items():
                key = tuple(x+y for x, y in zip(p, q))
                out[key] = out.get(key, F(0)) + c*d
        return Poly(out)
    __rmul__ = __mul__
    def __eq__(self, rhs): return self.terms == as_poly(rhs).terms
def as_poly(v): return v if isinstance(v, Poly) else Poly(v)

a, b, c, u, m, d, dp, p, q, e, k = (Poly.var(x) for x in Poly.names)
bi, ui = Poly.var('b', -1), Poly.var('u', -1)
pivot_u, t = c*(1-a*bi), c*ui
check('pivot convex coefficient u1', (a*bi)*b == a)
check('pivot convex coefficient x', a*bi+(1-a*bi) == 1)
check('pivot defect coefficient u1', t*a-(t-1)*b == (pivot_u-u)*(-b*ui))
check('pivot defect coefficient u2', t*pivot_u-c == (pivot_u-u)*t)

# Monomial substitution (5.33) -> (5.34) -> (5.3), all symbolic exponents.
check('scale exponent in (5.3)', (dp-d+1-e)+(d-2*e)+(2*m+2) == 2*m+3+dp-3*e)
check('density exponent in (5.3)', 6+2*(q+e-2)+p+2 == p+2*q+4+2*e)
check('conditioning exponent before weakening', 6+6*(q+e)+5*(k-1) == 5*(k-1)+6*q+6*e+6)
check('marked fraction exponent', (p+1)+2 == p+3)
check('logarithm exponent', -3-(p+1) == -(p+4))
check('union exponent after substitution', 2+1+1 == 4)
check('tube number exponent', 1+2 == 3)
check('sparse density margin (7.2)',
      (m+3)*F(1,2)-(2*m+3+dp)*F(1,4)+((p+2*q+4)*F(1,4)-2)*F(1,3)
      == (p+2*q-3*dp+5)*F(1,12))

D, C = F(33,8), F(15,4)
for label, got, expected in [
    ('six D-C', D-C, F(3,8)),
    ('six angular margin', 5-D, F(7,8)),
    ('six sparse margin combined', 4-D+(C-2)/3, F(11,24)),
    ('six sparse margin first-step', 4-D+(C-2)/4, F(5,16)),
    ('six low-cell margin', 6-D, F(15,8)),
    ('six old-cell small-scale margin', 1-D/12, F(21,32)),
    ('six angular exponent before error', D-5+F(1,4), F(-5,8)),
    ('six operator first-step loss', (6-D)/D, F(5,11)),
    ('six operator diagonal-limit loss', (6-F(29,7))/F(29,7), F(13,29)),
    ('eight operator diagonal-limit loss', (8-F(37,7))/F(37,7), F(19,37)),
]: check(label, got == expected)

slopes = [F(1,2)]
for j in range(8): slopes.append((2+slopes[-1]**2)/4)
check('slope table', slopes[:4] == [F(1,2), F(9,16), F(593,1024), F(2448801,4194304)])
check('dimension six profile table', [3+2*x for x in slopes[:4]] ==
      [F(4), F(33,8), F(2129,512), F(8740257,2097152)])
check('dimension eight profile table', [3+4*x for x in slopes[:4]] ==
      [F(5), F(21,4), F(1361,256), F(5594529,1048576)])
for n in (6,8):
    value = F(n+2,2); lim = F(4*n+5,7)
    for j in range(12):
        check(f'diagonal closed form n={n} j={j}', value == lim+(F(n+2,2)-lim)/8**j)
        check(f'diagonal domain n={n} j={j}', 3 < (value+3)/2 < value < n-1)
        nxt=(4*n+value+5)/8; density=(2*value+7)/4
        check(f'diagonal globalization n={n} j={j}', density <= nxt < n-1)
        value=nxt

# Appendix B: finite rational optimization, and signs by squaring positive numbers.
expected_B = [F(18,5),F(4),F(34,7),F(21,4),F(6),F(13,2),F(7),F(31,4),F(106,13),F(9),F(47,5)]
comparisons=[]
for n, expected in zip(range(5,16), expected_B):
    options=[(ell,min(F(n-ell+2),F(n*n+ell*ell+n-ell,2*n))) for ell in range(2,n+1)]
    B=max(x[1] for x in options)
    check(f'Appendix B exact benchmark n={n}', B==expected)
    A=2*n-5-B; check(f'Appendix B positive squaring base n={n}', A>0)
    is_positive=A*A > 2*(n-4)**2
    check(f'Appendix B sign n={n}', is_positive == (n in (6,8,10,11,13,15)))
    with localcontext() as ctx:
        ctx.prec=50
        kval=3+(2-Decimal(2).sqrt())*(n-4)
        comparisons.append({'n':n,'B':str(B),'K':f'{kval:.6f}',
                            'K_minus_B':f'{kval-Decimal(B.numerator)/Decimal(B.denominator):+.6f}',
                            'maximizers':[ell for ell,x in options if x==B]})

# A small exhaustive stress test of Lemma 4.2, independent of the Lean induction.
# Four singleton leaves, two children {0,1}, {2,3}, and their root.
nodes=[(0,), (1,), (2,), (3,), (0,1), (2,3), (0,1,2,3)]
subsets=list(product((0,1), repeat=4)); weights=list(product((F(0),F(1,2),F(1)), repeat=4))
configs=0; feasible_weights=0
for cap in product(range(2),range(2),range(2),range(2),range(3),range(3),range(5)):
    configs+=1
    def feasible(v): return all(sum(v[i] for i in node)<=b for node,b in zip(nodes,cap))
    optimum=max(sum(s) for s in subsets if feasible(s))
    rleft=min(cap[4],cap[0]+cap[1]); rright=min(cap[5],cap[2]+cap[3])
    recursive=min(cap[6],rleft+rright)
    if recursive!=optimum: raise AssertionError(('laminar integer optimum',cap))
    for w in weights:
        if feasible(w):
            feasible_weights+=1
            if sum(w)>recursive: raise AssertionError(('laminar fractional domination',cap,w))
check('exhaustive four-leaf laminar capacity stress test', True)

print(json.dumps({'status':'PASS','named_checks':len(checks),'checks':checks,
    'laminar_capacity_configurations':configs,'laminar_feasible_half_integral_weights':feasible_weights,
    'appendix_B':comparisons,
    'scope':'Exact algebra and finite tests only; no geometric Kakeya theorem certified.'}, indent=2))
