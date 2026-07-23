#!/usr/bin/env python3
"""Enumerate rigorous affine Type-II congruence families.

For a modulus M divisible by 24, this script enumerates two polynomial
specializations of the Type-II factor-pair identity and lists unit residues
r ≡ 1 (mod 24) not covered by either specialization.

The computation is finite exact arithmetic. A zero residual count would give
a finite congruence cover only after the emitted family schemas are formally
checked; a nonzero count is not evidence against the Erdős–Straus conjecture.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass(frozen=True)
class AffineFamily:
    kind: str
    a: int
    b: int | None
    c: int | None
    d: int
    modulus: int
    residue: int
    base_variable: int
    s0: int


def divisors(n: int) -> list[int]:
    if n <= 0:
        raise ValueError("divisors requires a positive integer")
    result: list[int] = []
    for value in range(1, math.isqrt(n) + 1):
        if n % value == 0:
            result.append(value)
            if value * value != n:
                result.append(n // value)
    return sorted(result)


def affine_families(modulus: int) -> list[AffineFamily]:
    """Return strict-safe affine Type-II congruences whose moduli divide M.

    Template C (c affine): fixed coprime a<b with d | a+b.
      p ≡ -d (mod 4ab), c=(p+d)/(4ab), s=(a+b)/d.

    Template B (b affine): fixed a,c,d with
      p ≡ -(4a²c+d) (mod 4acd), b=(p+d)/(4ac), s=(a+b)/d.

    The t=0 strict inequalities are checked. Since p, b/c, and s then grow
    monotonically, every later member of the progression is also strict.
    """
    if modulus % 24 != 0:
        raise ValueError("modulus must be divisible by 24")

    families: dict[tuple[int, int], AffineFamily] = {}

    # Fixed a,b; c grows by one each period.
    for a in divisors(modulus // 4):
        if modulus % (4 * a) != 0:
            continue
        for b in divisors(modulus // (4 * a)):
            family_modulus = 4 * a * b
            if modulus % family_modulus != 0 or not (a < b):
                continue
            if math.gcd(a, b) != 1:
                continue
            for d in divisors(a + b):
                if d % 4 != 3:
                    continue
                residue = (-d) % family_modulus
                if residue == 0:
                    continue
                c0 = (residue + d) // family_modulus
                s0 = (a + b) // d
                if c0 > 0 and b < residue * s0:
                    family = AffineFamily(
                        "c-affine", a, b, None, d,
                        family_modulus, residue, c0, s0,
                    )
                    families[(family_modulus, residue)] = family

    # Fixed a,c; b and s grow with the progression parameter.
    for a in divisors(modulus // 4):
        if modulus % (4 * a) != 0:
            continue
        for c in divisors(modulus // (4 * a)):
            quotient = modulus // (4 * a * c)
            for d in divisors(quotient):
                if d % 4 != 3:
                    continue
                family_modulus = 4 * a * c * d
                residue = (-4 * a * a * c - d) % family_modulus
                if residue == 0 or (residue + d) % (4 * a * c) != 0:
                    continue
                b0 = (residue + d) // (4 * a * c)
                if (a + b0) % d != 0:
                    continue
                s0 = (a + b0) // d
                if b0 > a and s0 > 0 and b0 < residue * s0:
                    family = AffineFamily(
                        "b-affine", a, None, c, d,
                        family_modulus, residue, b0, s0,
                    )
                    families[(family_modulus, residue)] = family

    return sorted(families.values(), key=lambda f: (f.modulus, f.residue))


def run(modulus: int) -> dict[str, object]:
    families = affine_families(modulus)
    population = [
        residue for residue in range(modulus)
        if residue % 24 == 1 and math.gcd(residue, modulus) == 1
    ]
    residual = [
        residue for residue in population
        if not any(
            residue % family.modulus == family.residue
            for family in families
        )
    ]
    return {
        "scope": "finite exact affine-family sieve; not a universal proof",
        "modulus": modulus,
        "population": "unit residues congruent to 1 modulo 24",
        "population_count": len(population),
        "family_congruence_count": len(families),
        "residual_count": len(residual),
        "residual_density": len(residual) / len(population),
        "residual_classes": residual,
        "families": [asdict(family) for family in families],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modulus", type=int, required=True)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    result = run(args.modulus)
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
