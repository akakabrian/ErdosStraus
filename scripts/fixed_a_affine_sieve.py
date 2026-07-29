#!/usr/bin/env python3
"""Finite affine residue sieve for the fixed-a Type-I family.

For a modulus M, restrict to fixed pairs (a,d) with 4*a | M and d | M.
Such a pair covers a residue r modulo M when

    r + a = 0 mod d,
    r + d = 0 mod 4*a.

Only unit residues r = 1 mod 24 are counted, matching the residual-prime
architecture. The output is a finite congruence sieve, not a universal proof.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def divisors(n: int) -> list[int]:
    result: list[int] = []
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            result.append(d)
            if d * d != n:
                result.append(n // d)
    return sorted(result)


def run(modulus: int) -> dict[str, object]:
    if modulus <= 0 or modulus % 24 != 0:
        raise ValueError("modulus must be a positive multiple of 24")

    residues = [
        r
        for r in range(modulus)
        if r % 24 == 1 and math.gcd(r, modulus) == 1
    ]
    modulus_divisors = divisors(modulus)
    covered_by: dict[int, list[tuple[int, int]]] = {r: [] for r in residues}
    useful_pairs: list[dict[str, object]] = []

    for a in range(1, modulus // 4 + 1):
        if modulus % (4 * a) != 0:
            continue
        for d in modulus_divisors:
            if d % 2 == 0:
                continue
            hits = [
                r
                for r in residues
                if (r + a) % d == 0 and (r + d) % (4 * a) == 0
            ]
            if not hits:
                continue
            useful_pairs.append({"a": a, "d": d, "covered_count": len(hits)})
            for r in hits:
                covered_by[r].append((a, d))

    residual = [r for r in residues if not covered_by[r]]
    return {
        "scope": "finite affine congruence sieve; not a universal proof",
        "modulus": modulus,
        "unit_residues_congruent_one_mod_24": len(residues),
        "useful_pair_count": len(useful_pairs),
        "covered_count": len(residues) - len(residual),
        "residual_count": len(residual),
        "residual_classes": residual,
        "useful_pairs": useful_pairs,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modulus", type=int, required=True)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()

    try:
        result = run(args.modulus)
    except ValueError as exc:
        parser.error(str(exc))
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
