#!/usr/bin/env python3
"""Second-pass review tests. No Lean executable is invoked by this script."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import importlib.util
import json
from math import comb, gcd, lcm
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
import check_axioms
import static_audit
import verification_guards as guards
from regression_tests import factor

ROOT=Path(__file__).resolve().parent

class ExecutionGuardTests(unittest.TestCase):
    def test_axiom_parser_regression_suite(self):
        self.assertEqual(check_axioms.self_test(),16)

    def test_exact_release_banners(self):
        for text in (
            'Lean (version 4.27.0)',
            'Lean (version 4.27.0, x86_64-unknown-linux-gnu, commit abc, Release)\n',
            'Lean (version 4.27.0, aarch64-apple-darwin, commit abc, Release)',
        ):
            with self.subTest(text=text):
                self.assertEqual(guards.validate_lean_version(text),'4.27.0')

    def test_reject_near_match_versions(self):
        for version in ('4.27.0-rc1','4.27.01','4.27.0+custom','4.28.0','4.2.7.0','v4.27.0'):
            with self.subTest(version=version):
                with self.assertRaises(ValueError):
                    guards.validate_lean_version(f'Lean (version {version}, Release)')
        for text in ('', 'arbitrary version 4.27.0',
                     'prefix Lean (version 4.27.0)',
                     'Lean (version 4.27.0)\nLean (version 4.27.0)'):
            with self.subTest(text=text):
                with self.assertRaises(ValueError): guards.validate_lean_version(text)

    def test_relative_lake_search_paths(self):
        workspace=Path('/some/workspace')
        result=guards.normalized_lean_path(
            '.lake/packages/mathlib/.lake/build/lib/lean:/upstream/absolute:./.lake/build/lib/lean',
            workspace,Path('/fresh/objects')).split(os.pathsep)
        self.assertEqual(result,[
            '/fresh/objects',
            '/some/workspace/.lake/packages/mathlib/.lake/build/lib/lean',
            '/upstream/absolute', '/some/workspace/.lake/build/lib/lean'])

    def test_snapshot_does_not_copy_cached_objects(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'root'; root.mkdir()
            (root/'Module.lean').write_text('theorem true_check : True := True.intro\n')
            (root/'Module.olean').write_bytes(b'STALE OBJECT')
            audit={'files':{'Module.lean':{'sha256':guards.sha256(root/'Module.lean')}}}
            stage=Path(temp)/'stage'
            guards.stage_sources(root,stage,audit)
            self.assertTrue((stage/'Module.lean').exists())
            self.assertFalse((stage/'Module.olean').exists())

    def test_snapshot_rejects_changed_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'root'; root.mkdir()
            (root/'Module.lean').write_text('one')
            audit={'files':{'Module.lean':{'sha256':guards.sha256(root/'Module.lean')}}}
            (root/'Module.lean').write_text('changed')
            with self.assertRaises(ValueError):
                guards.stage_sources(root,Path(temp)/'stage',audit)

    def test_snapshot_rejects_path_escape(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'root'; root.mkdir()
            with self.assertRaises(ValueError):
                guards.stage_sources(root,Path(temp)/'stage',
                    {'files':{'../escape.lean':{'sha256':'bad'}}})

    def audit_mutation(self,filename:str,append:str):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            shutil.copytree(ROOT/'PrimeAbundance',root/'PrimeAbundance')
            for name in ('PrimeAbundance.lean','GoalCheck.lean','TARGET.sha256'):
                shutil.copyfile(ROOT/name,root/name)
            with (root/filename).open('a') as out: out.write(append)
            with patch.object(static_audit,'ROOT',root):
                return static_audit.audit()

    def test_target_cannot_be_changed(self):
        with self.assertRaises(ValueError): self.audit_mutation('PrimeAbundance/Target.lean','\n')

    def test_goalcheck_cannot_be_changed(self):
        with self.assertRaises(ValueError): self.audit_mutation('GoalCheck.lean','\n')

    def test_printed_proof_reports_cannot_be_injected_elsewhere(self):
        with self.assertRaises(ValueError):
            self.audit_mutation('PrimeAbundance/Sums.lean','\n#eval "forged output"\n')

    def test_unsupported_import_not_silently_ignored(self):
        with self.assertRaises(ValueError):
            self.audit_mutation('PrimeAbundance/Sums.lean','\nimport Mathlib Unknown.Module\n')

    def test_missing_local_import_rejected(self):
        with self.assertRaises(ValueError):
            self.audit_mutation('PrimeAbundance/Sums.lean','\nimport PrimeAbundance.Absent\n')

    def test_kernel_bypass_option_rejected(self):
        with self.assertRaises(ValueError):
            self.audit_mutation('PrimeAbundance/Sums.lean','\nset_option debug.skipKernelTC true\n')

    def test_admission_in_code_rejected(self):
        with self.assertRaises(ValueError):
            self.audit_mutation('PrimeAbundance/Sums.lean','\ntheorem bad : True := by sorry\n')

    def test_admission_word_in_comment_is_not_code(self):
        report=self.audit_mutation('PrimeAbundance/Sums.lean','\n/- no sorry or axiom allowed /- nested -/ -/\n')
        self.assertEqual(report['status'],'PASSED_SOURCE_HYGIENE_ONLY')

    def test_missing_qualified_local_lemma_rejected(self):
        with self.assertRaisesRegex(ValueError, 'undefined qualified local reference'):
            self.audit_mutation('PrimeAbundance/Overlap.lean',
                '\ntheorem review_probe : True := by\n'
                '  have h := Late.deliberately_missing_review_lemma\n'
                '  exact True.intro\n')

    def test_qualified_local_lemma_needs_import(self):
        with self.assertRaisesRegex(ValueError, 'is not imported'):
            self.audit_mutation('PrimeAbundance/Arithmetic.lean',
                '\ntheorem review_probe : True := by\n'
                '  have h := Analytic.quantitative_abundance\n'
                '  exact True.intro\n')

    def test_known_wrong_namespace_removed(self):
        for filename in ('AnalyticBounds.lean','GlobalAbundance.lean'):
            text=(ROOT/'PrimeAbundance'/filename).read_text()
            self.assertNotIn('Real.isLittleO_log_rpow_rpow_atTop',text)
            self.assertIn('_root_.isLittleO_log_rpow_rpow_atTop',text)


def totient(n:int)->int:
    result=n
    for p in factor(n): result=result//p*(p-1)
    return result

def mathematical_checks()->dict:
    counts={}
    count=0
    for g in range(2,4097):
        value=sum(totient(d) for d in range(2,g+1) if g%d==0)
        assert value==g-1
        assert g <= 2*value
        count+=1
    counts['full_divisor_totient_split']=count
    count=0
    for k in range(17):
        partial=0
        for e in range(129):
            partial+=comb(e+k,k)
            assert partial==comb(e+k+1,k+1)
            count+=1
    counts['hockey_stick_identity']=count
    count=0
    for a in range(1,9):
        for b in range(1,9):
            for n in range(13):
                assert 2*n*F(1,48*a*b)==F(n,24*a*b)
                count+=1
    counts['block_coefficient_identity']=count
    # Genuine original packets with auxiliary roughness cutoff zero. These are
    # not numerical samples of the enormous eventual actual-cutoff regime.
    families=[[(333,1),(696,1)],[(333,1),(696,1),(333,9),(696,9)],
              [(6,1),(6,2),(6,3),(6,4)]]
    reports=[]; intervals=0
    for packets in families:
        for m,s in packets: assert m%3==0 and 0<s<m and m*m%s==0
        qs=[4*m-1 for m,s in packets]
        period=lcm(*qs)
        mu=sum((F(1,q) for q in qs),F(0)); delta=F(0)
        for i,(mi,si) in enumerate(packets):
            for j,(mj,sj) in enumerate(packets):
                g=gcd(qs[i],qs[j])
                if qs[i]<qs[j] and g>1 and (si-sj)%g==0:
                    delta+=F(g,qs[i]*qs[j])
        def firing(n):
            return sum((n+4*s)%q==0 for (m,s),q in zip(packets,qs))
        samples=[firing(n) for n in range(period)]
        variance=F(sum(t*t for t in samples),period)-mu*mu
        assert F(sum(samples),period)==mu
        assert variance<=mu+2*delta
        for start in (0,1,17,period-1):
            for h in (0,1,2,17,period+1):
                t=[samples[(start+k)%period] for k in range(h)]
                S1=sum(t); S2=sum(k*k for k in t); m=len(packets)
                assert S1>=h*mu-m
                assert S2<=h*(mu*mu+mu+2*delta)+m*m
                normalized=F(h)-2*S1/mu+S2/(mu*mu)
                raw_bound=h*(mu+2*delta)/(mu*mu)+2*m/mu+F(m*m)/(mu*mu)
                assert normalized<=raw_bound
                tail=sum(2*x<=mu for x in t)
                assert tail<=4*normalized
                intervals+=1
        reports.append({'packets':packets,'period':period,'mean':str(mu),
                        'unordered_overlap':str(delta),'variance':str(variance),
                        'factor_one_would_fail':variance>mu+delta})
    # This example actually detects, rather than merely tolerates, losing factor two.
    assert reports[0]['factor_one_would_fail']
    q,qq=1331,2783
    assert gcd(q,qq)==121
    rho=F(1,lcm(q,qq))
    assert rho==F(121,q*qq) and rho>F(11,q*qq)
    counts['normalized_moment_interval_cases']=intervals
    counts['full_prime_power_intersection_case']=1
    return {'counts':counts,'moment_examples':reports}

def main()->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json',type=Path)
    args=parser.parse_args()
    result=unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(ExecutionGuardTests))
    if not result.wasSuccessful(): return 1
    math=mathematical_checks()
    report={'status':'PASSED_REVIEW_REGRESSIONS_NOT_LEAN_VERIFICATION',
            'unit_tests':result.testsRun,'axiom_parser_synthetic_cases':check_axioms.self_test(),
            'mathematical_checks':math,'lean_executed':False,
            'asymptotic_theorem_verified':False,
            'test_scope':'Finite exact-arithmetic and verifier-control tests only.'}
    if args.json:
        args.json.parent.mkdir(parents=True,exist_ok=True)
        args.json.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return 0

if __name__=='__main__': raise SystemExit(main())
