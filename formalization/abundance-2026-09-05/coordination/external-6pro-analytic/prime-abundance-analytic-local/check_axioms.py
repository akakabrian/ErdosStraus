#!/usr/bin/env python3
"""Reject missing/duplicate reports and nonstandard axioms in actual Lean output."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGETS = (
    'PrimeAbundance.prime_abundance',
    'PrimeAbundance.Analytic.analytic_bounds',
    'PrimeAbundance.Analytic.quantitative_abundance',
    'PrimeAbundance.Analytic.relative_density',
    'PrimeAbundance.Late.finite_exceptional_bound',
)


def check(text: str) -> dict[str, list[str]]:
    if re.search(r'\berror\s*:', text, re.I):
        raise ValueError('Lean reported an error')
    if re.search(r'\bsorryAx\b|declaration uses [\'\"]?sorry', text):
        raise ValueError('Lean reported an admitted proof')
    output = {}
    for target in TARGETS:
        # Exact declaration at the start of a report line, not a matching suffix
        # inside e.g. Unrelated.PrimeAbundance.prime_abundance.
        name = re.escape(target)
        stem = rf"^[ \t]*(?:'{name}'|\"{name}\"|{name})[ \t]+"
        matches = re.findall(
            stem+r'depends on axioms:[ \t]*\[([^\]]*)\][ \t]*$',
            text, flags=re.M)
        empty = re.findall(
            stem+r'does not depend on any axioms[ \t]*$', text, flags=re.M)
        if len(matches)+len(empty) != 1:
            raise ValueError(f'Expected exactly one axiom report for {target}')
        used = set()
        if matches:
            used = {x.strip().strip("'\"") for x in matches[0].split(',') if x.strip()}
        unexpected = used-ALLOWED
        if unexpected:
            raise ValueError(f'{target}: rejected dependencies {sorted(unexpected)}')
        output[target] = sorted(used)
    return output


def self_test() -> int:
    base = '\n'.join(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in TARGETS)
    assert len(check(base)) == len(TARGETS)
    assert all(not v for v in check('\n'.join(f"'{n}' does not depend on any axioms" for n in TARGETS)).values())
    bad_cases = [
        '', base.replace(TARGETS[0], 'Wrong.statement', 1),
        base+'\n'+base.splitlines()[0],
        base.replace('Quot.sound', 'sorryAx', 1),
        base.replace('Quot.sound', 'Assume.mean_lower_bound', 1),
        base+'\nerror: unsolved goals',
        base.replace(TARGETS[2], TARGETS[2]+'.different', 1),
        base.replace(TARGETS[0], 'Unrelated.'+TARGETS[0], 1),
        base.replace(TARGETS[0], 'Not'+TARGETS[0], 1),
        base.replace(TARGETS[0], TARGETS[0]+"' trailing", 1),
        base.replace('depends on axioms: [', 'depends on axioms: [Unproved.fact, ', 1),
        base.replace('depends on axioms: [propext, Classical.choice, Quot.sound]',
                     'depends on axioms: [propext, Classical.choice, Quot.sound] extra', 1),
        '\n'.join(base.splitlines()[:-1]),
    ]
    for value in bad_cases:
        try:
            check(value)
        except ValueError:
            pass
        else:
            raise AssertionError('A negative audit test was accepted')
    multiline = base.replace('[propext, Classical.choice, Quot.sound]',
                             '[propext,\n Classical.choice,\n Quot.sound]')
    assert check(multiline) == check(base)
    return len(bad_cases)+3


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', nargs='?', type=Path)
    parser.add_argument('--json', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    try:
        if args.self_test:
            print(f'Axiom-report parser: {self_test()} synthetic guard tests passed. No Lean was run.')
            return 0
        if not args.log:
            parser.error('a log path or --self-test is required')
        result = check(args.log.read_text(encoding='utf-8'))
        if args.json:
            args.json.parent.mkdir(parents=True, exist_ok=True)
            args.json.write_text(json.dumps(result, indent=2)+'\n')
        print('Axiom-report text accepted for all required declarations; run provenance is checked by verify.sh.')
    except (OSError, ValueError) as exc:
        print(f'AXIOM AUDIT FAILED: {exc}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
