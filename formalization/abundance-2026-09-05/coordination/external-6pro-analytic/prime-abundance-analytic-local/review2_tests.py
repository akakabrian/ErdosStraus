#!/usr/bin/env python3
"""Second-review regressions; exact finite arithmetic and known source patterns only.

This is NOT a Lean parser, elaborator, or proof checker.  The numeric checks do
not establish any asymptotic theorem or validate that the edited tactics run.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import product, permutations
from math import gcd, prod
from pathlib import Path
import hashlib
import json
import re
import unittest
import static_audit

ROOT = Path(__file__).resolve().parent


def block(file: str, name: str) -> str:
    text = static_audit.strip_comments_and_strings((ROOT/'PrimeAbundance'/file).read_text())
    found = re.search(r'^(?:lemma|theorem)\s+'+re.escape(name)+r'\b', text, re.M)
    if not found:
        raise ValueError('Missing declaration '+name)
    end = re.search(r'^(?:lemma|theorem|def|abbrev)\s+', text[found.end():], re.M)
    return text[found.start():found.end()+end.start() if end else len(text)]


class RepairedSourcePatterns(unittest.TestCase):
    """These prevent reintroducing specific defects, not arbitrary tactic errors."""
    def test_no_consumed_distribution_rewrite(self):
        text = block('TensorSums.lean','product_weight_moment')
        self.assertIn('simp_rw [mul_sum]',text)
        self.assertIn('rw [sum_comm]',text)
        self.assertNotIn('rw [sum_comm, mul_sum]',text)

    def test_geometric_endpoints_are_specialized(self):
        text = block('TensorSums.lean','finite_geometric_identity')
        self.assertIn('sum_range_succ (fun j : ℕ => r^j) (J+1)',text)
        self.assertIn('pow_succ r (J+1)',text)

    def test_weighted_and_unweighted_sums_are_distinct(self):
        text = block('TensorSums.lean','finite_geometric_moment_identity')
        self.assertIn('sum_range_succ (fun j : ℕ => (j:ℝ)*r^j) (J+1)',text)
        self.assertIn('sum_range_succ (fun j : ℕ => r^j) (J+1)',text)
        self.assertNotIn('sum_range_succ, sum_range_succ',text)

    def test_prime_sum_has_typed_reindexing(self):
        text = block('PrimeProduct.lean','primeTuple_log_moment')
        self.assertIn('have hprimeSum',text)
        self.assertNotIn('← sum_coe_sort',text)
        self.assertIn('mul_le_mul_of_nonneg_right hm hlog',text)

    def test_prime_products_have_typed_reindexing(self):
        text = block('PrimeProduct.lean','primeTupleMass_times_V')
        self.assertIn('have hV',text)
        self.assertIn('have hresult',text)
        self.assertNotIn('← prod_coe_sort',text)

    def test_triple_rotation_handles_three_index_types(self):
        text = block('Sums.lean','sum_rotate_three')
        self.assertIn('{α β γ : Type*}',text)
        self.assertIn('∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t',text)
        self.assertEqual(text.count('Finset.sum_comm'),2)

    def test_divisor_sum_really_moves_outermost(self):
        text = block('Overlap.lean','diffCover_scale_sum')
        self.assertLess(text.index('rw [sum_rotate_three]'),text.index('intro d hd'))
        self.assertIn('Finset.sum_mul_sum',text)
        self.assertNotIn('rw [sum_comm]',text)

    def test_pair_budget_explicit_before_aggregation(self):
        text = block('FiniteTransfer.lean','second_moment_upper')
        self.assertIn('mul_add,mul_sum,sum_add_distrib',text)
        self.assertIn('rw [hbase,hdiag,hforward,hbackward]',text)
        self.assertNotIn('simp_rw [sum_add_distrib,←mul_sum]',text)

    def test_target_and_entrypoint_locks(self):
        for rel, expected in [
            ('PrimeAbundance/Target.lean',static_audit.LOCKED_TARGET_SHA256),
            ('GoalCheck.lean',static_audit.LOCKED_GOALCHECK_SHA256),
        ]:
            self.assertEqual(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest(),expected)


def divisors(n: int) -> list[int]:
    if n < 1:
        return []
    return [d for d in range(1,n+1) if n%d == 0]


def phi(n: int) -> int:
    return sum(gcd(k,n)==1 for k in range(1,n+1))


def exact_checks() -> dict:
    counts: dict[str,int] = {}
    count = 0
    for r in [F(-2),F(-1,3),F(0),F(1,10),F(1,2),F(9,10),F(1),F(2)]:
        for J in range(21):
            S=sum((r**j for j in range(J+1)),F())
            M=sum((j*r**j for j in range(J+1)),F())
            assert (1-r)*S == 1-r**(J+1)
            assert (1-r)*M == r*S-(J+1)*r**(J+1)
            assert sum((r**j for j in range(J+2)),F()) == S+r**(J+1)
            assert sum((j*r**j for j in range(J+2)),F()) == M+(J+1)*r**(J+1)
            if 0<=r<1:
                assert M <= r/(1-r)*S
            count+=1
    counts['finite_geometric_identities_and_endpoints']=count

    count=0
    for dimension in range(5):
        for size in range(4):
            for seed in range(5):
                f=[[F(((i+2)*j+seed)%7,i+j+2) for j in range(size)] for i in range(dimension)]
                if dimension and seed==4:
                    f[dimension//2]=[F() for _ in range(size)]
                g=[[F((i+3)*j-2*seed-1,j+1) for j in range(size)] for i in range(dimension)]
                masses=[sum(row,F()) for row in f]
                moments=[sum((a*b for a,b in zip(fr,gr)),F()) for fr,gr in zip(f,g)]
                b=[moment/mass+F(seed,3) if mass else F() for moment,mass in zip(moments,masses)]
                assert all(moment<=bound*mass for moment,bound,mass in zip(moments,b,masses))
                lhs=sum((prod((f[i][x[i]] for i in range(dimension)),start=F(1))*
                         sum((g[i][x[i]] for i in range(dimension)),F())
                         for x in product(range(size),repeat=dimension)),F())
                expanded=sum((moments[i]*prod((masses[j] for j in range(dimension) if i!=j),start=F(1))
                              for i in range(dimension)),F())
                rhs=prod(masses,start=F(1))*sum(b,F())
                assert lhs==expanded and lhs<=rhs
                count+=1
    counts['tensor_product_moments_with_empty_and_zero_mass_cases']=count

    count=0
    for primes in [(),(2,),(3,),(2,3),(2,5),(3,5),(2,3,5)]:
        V=prod((1-F(1,p) for p in primes),start=F(1))
        for J in range(6):
            tuples=list(product(range(J+1),repeat=len(primes)))
            nums=[prod(p**e for p,e in zip(primes,t)) for t in tuples]
            assert len(set(nums))==len(nums)
            mass=sum((F(1,n) for n in nums),F())
            local=[sum((F(1,p)**j for j in range(J+1)),F()) for p in primes]
            assert mass==prod(local,start=F(1))
            assert mass*V==prod((1-F(1,p)**(J+1) for p in primes),start=F(1))
            # Positive integer coordinate coefficients exercise pulling log(p)
            # outside the moment; this does not numerically assert a log identity.
            coeff=[2+i for i in range(len(primes))]
            moment=sum((F(sum(c*e for c,e in zip(coeff,t)),n) for t,n in zip(tuples,nums)),F())
            assert moment<=mass*sum((F(c,p-1) for c,p in zip(coeff,primes)),F())
            count+=1
    counts['prime_tuple_product_and_coordinate_moment_cases']=count

    count=0
    for sa in range(5):
        for sb in range(5):
            for sc in range(5):
                # Deliberately distinct index types and unbalanced ranges.
                A=[('u',i) for i in range(sa)]
                B=[f'v{j}' for j in range(sb)]
                C=[10+k for k in range(sc)]
                def f(a,b,c):
                    i=a[1]; j=int(b[1:]); k=c-10
                    return F((i+1)**2+7*(j+1)+31*(k+1)+(i-j)*(k+2),1+i+j+k)
                lhs=sum((f(a,b,c) for a in A for b in B for c in C),F())
                rhs=sum((f(a,b,c) for c in C for a in A for b in B),F())
                assert lhs==rhs
                count+=1
    counts['three_sum_rotations_with_distinct_index_types']=count
    # A numeric witness that the prematurely introduced outer variable would
    # describe a different per-index expression even when all types are naturals.
    scales=(1,2); ds=(1,2,3)
    def witness(u,v,d): return u+10*v+100*d
    correct_d1=sum(witness(u,v,1) for u in scales for v in scales)
    wrong_v1=sum(witness(u,1,d) for u in scales for d in ds)
    assert (correct_d1,wrong_v1)==(466,1269)

    count=0
    ranges=[((),()),((1,),()),((1,2),(3,4,5)),(tuple(range(1,10)),tuple(range(3,12)))]
    rays=[(1,2),(1,3),(2,3),(2,5),(3,5),(4,5)]
    for (a,b),(c,e) in permutations(rays,2):
        D=abs(a*e-c*b)
        assert D>0
        for w in (0,1,2,4):
            for U,V in ranges:
                lhs=2*sum((F(phi(d),(12*a*b*u-1)*(12*c*e*v-1))
                           for u in U for v in V for d in divisors(D)
                           if w<d and (12*a*b*u-1)%d==0 and (12*c*e*v-1)%d==0),F())
                rhs=2*sum((phi(d)*sum((F(1,12*a*b*u-1) for u in U if (12*a*b*u-1)%d==0),F())*
                           sum((F(1,12*c*e*v-1) for v in V if (12*c*e*v-1)%d==0),F())
                           for d in divisors(D) if w<d),F())
                assert lhs==rhs
                count+=1
    counts['full_divisor_separable_overlap_identities']=count

    count=0
    for m in range(8):
        for H in (0,1,7,100):
            for seed in range(4):
                a=[F(i+1,11+seed+i) for i in range(m)]
                o=[[F(((i+1)*(j+2)+seed)%5,3+i+j) if i<j else F() for j in range(m)] for i in range(m)]
                lhs=sum((H*(a[i]*a[j]+(a[i] if i==j else 0)+o[i][j]+o[j][i])+1
                         for i in range(m) for j in range(m)),F())
                mu=sum(a,F()); lam=sum((v for row in o for v in row),F())
                rhs=H*(mu**2+mu+2*lam)+m**2
                assert lhs==rhs
                count+=1
    counts['second_moment_budget_diagonal_orientations_and_endpoint']=count
    return {'exact_arithmetic_cases':sum(counts.values()),'cases_by_group':counts,
            'wrong_outer_variable_witness':{'correct_divisor_1_fiber':correct_d1,'incorrect_scale_1_fiber':wrong_v1},
            'lean_executed':False,'asymptotic_theorem_tested':False,
            'qualification':'Finite identities and known-pattern checks only; not Lean verification.'}


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json',type=Path)
    args=parser.parse_args()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(RepairedSourcePatterns)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful(): return 1
    report=exact_checks()
    report['source_pattern_test_methods']=result.testsRun
    report['passed']=True
    if args.json:
        args.json.parent.mkdir(parents=True,exist_ok=True)
        args.json.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return 0

if __name__=='__main__': raise SystemExit(main())
