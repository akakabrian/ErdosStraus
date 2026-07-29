#!/usr/bin/env python3
"""Exact fixed-a Type-I profiler for Erdős--Straus residual primes.

For positive integers a,c,d,s with

    p + a = d*s,
    p + d = 4*a*c,
    1 <= a < p,
    0 < d < p,

the Type-I certificate with b=1 has strict denominators

    X = a*c,
    Y = a*c*s,
    Z = p*c*s.

Equivalently, for each a the script factors p+a and searches a proper divisor
d such that p+d is divisible by 4*a. Every emitted witness is checked by
exact integer arithmetic. Finite coverage is not a universal proof.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterator

from consecutive_gate_profiler import factorize, residual_primes, small_primes

MORDELL_RESIDUES = frozenset({1, 121, 169, 289, 361, 529})


@dataclass(frozen=True)
class FixedAWitness:
    p: int
    a: int
    d: int
    c: int
    s: int
    x: int
    y: int
    z: int


def divisors(factors: list[tuple[int, int]]) -> list[int]:
    values = [1]
    for prime, exponent in factors:
        powers = [prime**e for e in range(exponent + 1)]
        values = [value * power for value in values for power in powers]
    return sorted(values)


def verify_witness(witness: FixedAWitness) -> None:
    p, a, d, c, s = (
        witness.p,
        witness.a,
        witness.d,
        witness.c,
        witness.s,
    )
    if not (1 <= a < p and 0 < d < p and 0 < c and 0 < s):
        raise AssertionError("fixed-a positivity or proper-divisor condition failed")
    if p + a != d * s or p + d != 4 * a * c:
        raise AssertionError("fixed-a Type-I equations failed")
    if not (1 <= witness.x < witness.y < witness.z):
        raise AssertionError("strict denominator order failed")
    if 4 * witness.x * witness.y * witness.z != p * (
        witness.x * witness.y + witness.x * witness.z + witness.y * witness.z
    ):
        raise AssertionError("polynomial Erdős--Straus identity failed")


def witness_for_a(
    p: int, a: int, trial_primes: list[int]
) -> FixedAWitness | None:
    if not (1 <= a < p):
        return None
    for d in divisors(factorize(p + a, trial_primes)):
        if d >= p:
            break
        denominator = 4 * a
        if (p + d) % denominator != 0:
            continue
        c = (p + d) // denominator
        s = (p + a) // d
        witness = FixedAWitness(
            p=p,
            a=a,
            d=d,
            c=c,
            s=s,
            x=a * c,
            y=a * c * s,
            z=p * c * s,
        )
        verify_witness(witness)
        return witness
    return None


def first_witness(
    p: int, max_a: int, trial_primes: list[int]
) -> FixedAWitness | None:
    for a in range(1, min(max_a, p - 1) + 1):
        witness = witness_for_a(p, a, trial_primes)
        if witness is not None:
            return witness
    return None


def segmented_mordell_primes(
    start: int, limit: int, base_primes: list[int], chunk_size: int
) -> Iterator[int]:
    low0 = max(2, start)
    for low in range(low0, limit + 1, chunk_size):
        high = min(limit + 1, low + chunk_size)
        sieve = bytearray(b"\x01") * (high - low)
        root = math.isqrt(high - 1)
        for prime in base_primes:
            if prime > root:
                break
            first = max(prime * prime, ((low + prime - 1) // prime) * prime)
            if first < high:
                sieve[first - low : high - low : prime] = b"\x00" * (
                    ((high - 1 - first) // prime) + 1
                )
        for offset, is_prime in enumerate(sieve):
            if is_prime:
                candidate = low + offset
                if candidate % 840 in MORDELL_RESIDUES:
                    yield candidate


def counter_json(counter: Counter[int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def run_full(limit: int, max_a: int) -> dict[str, object]:
    trial_primes = small_primes(math.isqrt(limit + max_a) + 1)
    primes: Iterator[int] = residual_primes(limit)
    return profile(
        primes,
        73,
        limit,
        max_a,
        trial_primes,
        "primes p congruent to 1 modulo 24",
    )


def run_mordell(
    start: int, limit: int, max_a: int, chunk_size: int
) -> dict[str, object]:
    base_primes = small_primes(math.isqrt(limit + max_a) + 1)
    primes = segmented_mordell_primes(start, limit, base_primes, chunk_size)
    result = profile(
        primes,
        start,
        limit,
        max_a,
        base_primes,
        "primes in the six Mordell residue classes modulo 840",
    )
    result["mordell_residues"] = sorted(MORDELL_RESIDUES)
    result["chunk_size"] = chunk_size
    return result


def profile(
    primes: Iterator[int],
    start: int,
    limit: int,
    max_a: int,
    trial_primes: list[int],
    population: str,
) -> dict[str, object]:
    started = time.perf_counter()
    checked = 0
    distribution: Counter[int] = Counter()
    unresolved: list[int] = []
    record_witnesses: list[dict[str, int]] = []
    largest_a = -1

    for p in primes:
        checked += 1
        witness = first_witness(p, max_a, trial_primes)
        if witness is None:
            unresolved.append(p)
            continue
        distribution[witness.a] += 1
        if witness.a > largest_a:
            largest_a = witness.a
            record_witnesses.append(asdict(witness))

    cumulative_bounds = [1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000, max_a]
    cumulative = {
        str(bound): sum(count for a, count in distribution.items() if a <= bound)
        for bound in sorted(set(bound for bound in cumulative_bounds if bound <= max_a))
    }

    return {
        "scope": "finite exact computation; not a universal proof",
        "searched_population": population,
        "start": start,
        "limit": limit,
        "max_a_searched": max_a,
        "primes_checked": checked,
        "resolved_count": checked - len(unresolved),
        "unresolved_count": len(unresolved),
        "unresolved_primes": unresolved,
        "largest_first_a": None if largest_a < 0 else largest_a,
        "first_a_distribution": counter_json(distribution),
        "cumulative_coverage": cumulative,
        "record_witnesses": record_witnesses,
        "elapsed_seconds": time.perf_counter() - started,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, required=True)
    parser.add_argument("--start", type=int, default=73)
    parser.add_argument("--max-a", type=int, default=1000)
    parser.add_argument("--mordell-only", action="store_true")
    parser.add_argument("--chunk-size", type=int, default=5_000_000)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()

    if args.start > args.limit:
        parser.error("start must not exceed limit")
    if args.max_a < 1:
        parser.error("max-a must be positive")
    if args.mordell_only:
        result = run_mordell(args.start, args.limit, args.max_a, args.chunk_size)
    else:
        if args.start != 73:
            parser.error("custom --start requires --mordell-only")
        result = run_full(args.limit, args.max_a)

    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
