#!/usr/bin/env python3
"""Exact d=11 gate audit and legacy-component regression checker.

The earlier specialized d=11 script treated each entire prime power q^e as an
indivisible component and required both selected sides to be nonempty. That is
not equivalent to choosing arbitrary coprime divisors of x:

* either divisor may be 1;
* for each prime q^e || x, one may assign q^j with 1 <= j <= e to one side.

This script delegates the exact criterion to ``fixed_gate_automaton.py`` and
retains the former full-component model only to expose finite disagreements.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import Counter
from pathlib import Path
from typing import Iterator

from fixed_gate_automaton import automaton_witness, factorize


MODULUS = 11


def legacy_full_component_witness(x: int, modulus: int = MODULUS) -> tuple[int, int] | None:
    """Reproduce the incomplete former model for regression comparison."""
    states: dict[tuple[int, int, bool, bool], tuple[int, int]] = {
        (1 % modulus, 1 % modulus, False, False): (1, 1)
    }
    for factor in factorize(x):
        value = factor.prime**factor.exponent
        next_states = dict(states)
        for (left_residue, right_residue, used_left, used_right), (
            left,
            right,
        ) in states.items():
            next_states.setdefault(
                (
                    (left_residue * value) % modulus,
                    right_residue,
                    True,
                    used_right,
                ),
                (left * value, right),
            )
            next_states.setdefault(
                (
                    left_residue,
                    (right_residue * value) % modulus,
                    used_left,
                    True,
                ),
                (left, right * value),
            )
        states = next_states

    for (left_residue, right_residue, used_left, used_right), (
        left,
        right,
    ) in states.items():
        if used_left and used_right and (left_residue + right_residue) % modulus == 0:
            return tuple(sorted((left, right)))
    return None


def prime_sieve(limit: int) -> bytearray:
    if limit < 1:
        return bytearray(limit + 1)
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for n in range(2, math.isqrt(limit) + 1):
        if sieve[n]:
            start = n * n
            sieve[start : limit + 1 : n] = b"\x00" * (
                ((limit - start) // n) + 1
            )
    return sieve


def residual_primes(limit: int) -> Iterator[int]:
    sieve = prime_sieve(limit)
    for p in range(73, limit + 1, 24):
        if sieve[p]:
            yield p


def audit_sequence(limit: int) -> dict[str, object]:
    """Compare exact and legacy d=11 decisions after exact d=3 and d=7 failure."""
    counts: Counter[str] = Counter()
    disagreements: list[dict[str, object]] = []

    for p in residual_primes(limit):
        x3 = (p + 3) // 4
        if automaton_witness(x3, 3) is not None:
            counts["d3_success"] += 1
            continue

        x7 = (p + 7) // 4
        if automaton_witness(x7, 7) is not None:
            counts["d7_success_after_d3_failure"] += 1
            continue

        x11 = (p + 11) // 4
        exact = automaton_witness(x11, 11)
        legacy = legacy_full_component_witness(x11, 11)
        counts["reached_d11"] += 1
        counts["d11_exact_success" if exact else "d11_exact_failure"] += 1
        counts["d11_legacy_success" if legacy else "d11_legacy_failure"] += 1

        if exact is not None and legacy is None:
            disagreements.append(
                {
                    "p": p,
                    "x3": x3,
                    "x7": x7,
                    "x11": x11,
                    "factorization_x11": [
                        {"prime": factor.prime, "exponent": factor.exponent}
                        for factor in factorize(x11)
                    ],
                    "exact_witness": list(exact),
                    "legacy_witness": None,
                }
            )
        elif exact is None and legacy is not None:
            raise AssertionError("the legacy model cannot be stronger than the exact model")

    return {
        "scope": "finite exact audit; not a universal proof",
        "limit": limit,
        "counts": dict(sorted(counts.items())),
        "legacy_false_negative_count": len(disagreements),
        "first_legacy_false_negatives": disagreements[:20],
        "regressions": [
            {
                "x": 43**2,
                "factorization": "43^2",
                "exact_witness": list(automaton_witness(43**2, 11) or ()),
                "legacy_witness": legacy_full_component_witness(43**2, 11),
                "reason": "divisor 1 and a partial prime-power exponent are valid",
            },
            {
                "p": 4201,
                "x11": 1053,
                "factorization": "3^4*13",
                "exact_witness": list(automaton_witness(1053, 11) or ()),
                "legacy_witness": legacy_full_component_witness(1053, 11),
                "reason": "the valid pair (9,13) uses 3^2 from the 3^4 factor",
            },
        ],
    }


def profile_csv(input_csv: Path, output_csv: Path | None) -> dict[str, object]:
    """Recheck rows whose committed first Type-II witness occurs after d=11."""
    rows: list[dict[str, object]] = []
    with input_csv.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if int(row["k"]) < 3:
                continue
            p = int(row["p"])
            x11 = (p + 11) // 4
            exact = automaton_witness(x11, 11)
            legacy = legacy_full_component_witness(x11, 11)
            rows.append(
                {
                    "p": p,
                    "x11": x11,
                    "exact_d11_witness": exact,
                    "legacy_d11_witness": legacy,
                }
            )

    if output_csv is not None:
        output_csv.parent.mkdir(parents=True, exist_ok=True)
        with output_csv.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=[
                    "p",
                    "x11",
                    "exact_d11_witness",
                    "legacy_d11_witness",
                ],
            )
            writer.writeheader()
            writer.writerows(rows)

    return {
        "rows_checked": len(rows),
        "exact_successes": sum(row["exact_d11_witness"] is not None for row in rows),
        "legacy_successes": sum(row["legacy_d11_witness"] is not None for row in rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-limit", type=int)
    parser.add_argument("--input-csv", type=Path)
    parser.add_argument("--output-csv", type=Path)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()

    result: dict[str, object] = {}
    if args.audit_limit is not None:
        result["sequence_audit"] = audit_sequence(args.audit_limit)
    if args.input_csv is not None:
        result["csv_profile"] = profile_csv(args.input_csv, args.output_csv)
    if not result:
        parser.error("provide --audit-limit or --input-csv")

    text = json.dumps(result, indent=2, sort_keys=True, default=list)
    print(text)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
