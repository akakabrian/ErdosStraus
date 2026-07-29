#!/usr/bin/env python3
"""Profile simultaneous failure of the global unit gate and bounded complete gates.

The unit Type-I gate fails exactly when p+1 has no odd prime divisor congruent
to 3 modulo 4. For those residual primes, this script finds the first
successful complete two-fraction factorization among consecutive offsets
0..max_k.

Finite output is falsification evidence only; it does not prove a universal
offset bound.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from dataclasses import asdict
from pathlib import Path

from consecutive_gate_profiler import (
    first_complete_witness,
    residual_primes,
    small_primes,
    unit_type_i_witness,
)


def counter_to_json(counter: Counter[int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def run(limit: int, max_k: int) -> dict[str, object]:
    max_x = (limit + 3) // 4 + max_k
    trial_primes = small_primes(math.isqrt(max(limit + 1, max_x)) + 1)

    checked = 0
    unit_successes = 0
    unit_failures = 0
    first_offset_distribution: Counter[int] = Counter()
    unresolved: list[int] = []
    record = None

    for p in residual_primes(limit):
        checked += 1
        if unit_type_i_witness(p, trial_primes) is not None:
            unit_successes += 1
            continue

        unit_failures += 1
        witness = first_complete_witness(p, max_k, trial_primes)
        if witness is None:
            unresolved.append(p)
            continue

        first_offset_distribution[witness.k] += 1
        if record is None or (witness.k, witness.p) > (record.k, record.p):
            record = witness

    return {
        "scope": "finite exact computation; not a universal proof",
        "limit": limit,
        "max_k": max_k,
        "residual_primes_checked": checked,
        "unit_gate_success_count": unit_successes,
        "unit_gate_failure_count": unit_failures,
        "first_complete_offset_distribution_after_unit_failure": counter_to_json(
            first_offset_distribution
        ),
        "largest_first_complete_k_after_unit_failure": max(
            first_offset_distribution, default=None
        ),
        "largest_first_complete_k_witness": asdict(record) if record else None,
        "unresolved_count": len(unresolved),
        "unresolved_primes": unresolved,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, required=True)
    parser.add_argument("--max-k", type=int, default=40)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()

    result = run(args.limit, args.max_k)
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
