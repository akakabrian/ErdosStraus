#!/usr/bin/env python3
"""Segmented exact Type-II profiler for Mordell-residue primes.

This companion to ``typeii_profiler.py`` avoids a full-range sieve. It scans
primes in the six classical Mordell classes modulo 840, searches offsets in a
specified range, and verifies every certificate with exact integer arithmetic.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from collections import Counter
from pathlib import Path
from typing import Iterator

from typeii_profiler import find_first_witness, small_primes

MORDELL_RESIDUES = frozenset({1, 121, 169, 289, 361, 529})


def segmented_mordell_primes(
    start: int, limit: int, base_primes: list[int], chunk_size: int
) -> Iterator[int]:
    """Yield primes in [start, limit] whose residue modulo 840 is Mordell-residual."""
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


def run(start: int, limit: int, max_k: int, chunk_size: int) -> dict[str, object]:
    if start > limit:
        raise ValueError("start must not exceed limit")
    if limit < 2:
        raise ValueError("limit must be at least 2")
    if max_k < 0:
        raise ValueError("max-k must be nonnegative")
    if chunk_size <= 0:
        raise ValueError("chunk-size must be positive")

    base_primes = small_primes(math.isqrt(limit) + 1)
    max_x = (limit + 4 * max_k + 3) // 4
    trial_limit = math.isqrt(max_x) + 1
    trial_primes = [prime for prime in base_primes if prime <= trial_limit]

    started = time.perf_counter()
    checked = 0
    unresolved: list[int] = []
    distribution: Counter[int] = Counter()
    record_witnesses: list[dict[str, object]] = []
    largest_k = -1

    for prime in segmented_mordell_primes(start, limit, base_primes, chunk_size):
        checked += 1
        witness = find_first_witness(prime, max_k, trial_primes)
        if witness is None:
            unresolved.append(prime)
            continue
        distribution[witness.k] += 1
        if witness.k > largest_k:
            largest_k = witness.k
            record_witnesses.append(witness.__dict__)

    return {
        "scope": "finite exact computation; not a universal proof",
        "searched_population": "primes in Mordell residue classes modulo 840",
        "mordell_residues": sorted(MORDELL_RESIDUES),
        "start": start,
        "limit": limit,
        "max_k_searched": max_k,
        "chunk_size": chunk_size,
        "primes_checked": checked,
        "unresolved_count": len(unresolved),
        "unresolved_primes": unresolved,
        "largest_first_witness_k": None if largest_k < 0 else largest_k,
        "first_witness_distribution": {
            str(k): count for k, count in sorted(distribution.items())
        },
        "record_witnesses": record_witnesses,
        "elapsed_seconds": time.perf_counter() - started,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--limit", type=int, required=True)
    parser.add_argument("--max-k", type=int, default=80)
    parser.add_argument("--chunk-size", type=int, default=5_000_000)
    parser.add_argument("--json", type=Path, help="optional JSON output path")
    args = parser.parse_args()

    try:
        result = run(args.start, args.limit, args.max_k, args.chunk_size)
    except ValueError as exc:
        parser.error(str(exc))

    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n", encoding="utf-8")
    return 0 if result["unresolved_count"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
