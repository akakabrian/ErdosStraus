#!/usr/bin/env python3
"""Exact Type-II profiler for residual Erdős–Straus primes.

Searches primes p ≡ 1 (mod 24). For x=(p+3)/4+k and D=4k+3,
it enumerates divisors q of x^2 with q<x and D | q+x. Each hit is
normalized to the coprime factor-pair certificate used by the Lean library.
All verification is exact integer arithmetic.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Iterator


@dataclass(frozen=True)
class Witness:
    p: int
    x: int
    k: int
    d: int
    q: int
    a: int
    b: int
    c: int
    s: int
    a_is_one: bool
    x_factorization: str
    d_factorization: str


def prime_sieve(limit: int) -> bytearray:
    if limit < 1:
        return bytearray(limit + 1)
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for n in range(2, math.isqrt(limit) + 1):
        if sieve[n]:
            start = n * n
            sieve[start : limit + 1 : n] = b"\x00" * (((limit - start) // n) + 1)
    return sieve


def small_primes(limit: int) -> list[int]:
    sieve = prime_sieve(limit)
    return [n for n in range(2, limit + 1) if sieve[n]]


def factorize(n: int, primes: Iterable[int]) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("factorization requires n >= 1")
    result: list[tuple[int, int]] = []
    rem = n
    for p in primes:
        if p * p > rem:
            break
        if rem % p == 0:
            exponent = 0
            while rem % p == 0:
                rem //= p
                exponent += 1
            result.append((p, exponent))
        if rem == 1:
            break
    if rem > 1:
        result.append((rem, 1))
    return result


def format_factorization(factors: list[tuple[int, int]]) -> str:
    if not factors:
        return "1"
    return "*".join(str(p) if e == 1 else f"{p}^{e}" for p, e in factors)


def divisors_of_square_below_x(
    factors: list[tuple[int, int]], x: int
) -> list[int]:
    divisors = [1]
    for prime, exponent in factors:
        powers = [1]
        for _ in range(2 * exponent):
            powers.append(powers[-1] * prime)
        divisors = [d * power for d in divisors for power in powers if d * power < x]
    return sorted(set(divisors))


def normalize_and_verify(
    p: int,
    x: int,
    k: int,
    d: int,
    q: int,
    x_factors: list[tuple[int, int]],
    d_factors: list[tuple[int, int]],
) -> Witness:
    if not (p > 3 and x > 0 and d > 0 and q > 0 and q < x):
        raise ValueError("nonpositive or non-strict candidate")
    if p + d != 4 * x:
        raise ValueError("offset identity failed")
    if (x * x) % q != 0:
        raise ValueError("q does not divide x^2")
    if (q + x) % d != 0:
        raise ValueError("opposite residue condition failed")

    g = math.gcd(x, q)
    a = q // g
    b = x // g
    if math.gcd(a, b) != 1:
        raise ValueError("normalization did not produce coprime factors")
    if g % a != 0:
        raise ValueError("q | x^2 failed to imply a | gcd(x,q)")
    c = g // a
    if (a + b) % d != 0:
        raise ValueError("normalized residue cancellation failed")
    s = (a + b) // d

    if not (a > 0 and a < b and c > 0 and s > 0 and b < p * s):
        raise ValueError("strict factor-pair inequalities failed")
    if p + d != 4 * a * b * c:
        raise ValueError("factor-pair product identity failed")
    if a + b != d * s:
        raise ValueError("factor-pair residue identity failed")

    den_x = a * b * c
    den_y = p * a * c * s
    den_z = p * b * c * s
    if not (1 <= den_x < den_y < den_z):
        raise ValueError("strict denominator order failed")
    if 4 * den_x * den_y * den_z != p * (
        den_x * den_y + den_x * den_z + den_y * den_z
    ):
        raise ValueError("polynomial Erdős–Straus identity failed")

    return Witness(
        p=p,
        x=x,
        k=k,
        d=d,
        q=q,
        a=a,
        b=b,
        c=c,
        s=s,
        a_is_one=(a == 1),
        x_factorization=format_factorization(x_factors),
        d_factorization=format_factorization(d_factors),
    )


def find_first_witness(
    p: int, max_k: int, trial_primes: list[int]
) -> Witness | None:
    for k in range(max_k + 1):
        x = (p + 3) // 4 + k
        d = 4 * k + 3
        if d >= p:
            break
        x_factors = factorize(x, trial_primes)
        d_factors = factorize(d, trial_primes)
        for q in divisors_of_square_below_x(x_factors, x):
            if (q + x) % d == 0:
                return normalize_and_verify(p, x, k, d, q, x_factors, d_factors)
    return None


def iter_residual_primes(limit: int) -> Iterator[int]:
    sieve = prime_sieve(limit)
    for p in range(73, limit + 1, 24):
        if sieve[p]:
            yield p


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(limit: int, max_k: int, csv_path: Path | None) -> dict[str, object]:
    if limit < 73:
        raise ValueError("limit must be at least 73")
    if max_k < 0:
        raise ValueError("max-k must be nonnegative")

    trial_primes = small_primes(math.isqrt((limit + 3) // 4 + max_k) + 1)
    witnesses: list[Witness] = []
    unresolved: list[int] = []
    started = time.perf_counter()

    for p in iter_residual_primes(limit):
        witness = find_first_witness(p, max_k, trial_primes)
        if witness is None:
            unresolved.append(p)
        else:
            witnesses.append(witness)

    elapsed = time.perf_counter() - started
    coverage_counts = {
        str(bound): sum(w.k <= bound for w in witnesses)
        for bound in (0, 1, 2, 5, 10, 15, max_k)
        if bound <= max_k
    }

    result: dict[str, object] = {
        "scope": "finite exact computation; not a universal proof",
        "limit": limit,
        "max_k": max_k,
        "primes_checked": len(witnesses) + len(unresolved),
        "resolved": len(witnesses),
        "unresolved_count": len(unresolved),
        "unresolved_primes": unresolved,
        "largest_first_witness_k": max((w.k for w in witnesses), default=None),
        "largest_d": max((w.d for w in witnesses), default=None),
        "a_equals_one": sum(w.a_is_one for w in witnesses),
        "nontrivial_a": sum(not w.a_is_one for w in witnesses),
        "coverage_counts": coverage_counts,
        "elapsed_seconds": elapsed,
    }

    if witnesses:
        record = max(witnesses, key=lambda w: (w.k, w.p))
        result["record_witness"] = asdict(record)

    if csv_path is not None:
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        fieldnames = list(asdict(witnesses[0]).keys()) if witnesses else list(Witness.__annotations__)
        with csv_path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(asdict(w) for w in witnesses)
        result["csv_path"] = str(csv_path)
        result["csv_sha256"] = sha256_file(csv_path)

    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, required=True, help="inclusive prime limit")
    parser.add_argument("--max-k", type=int, default=26, help="largest offset index to search")
    parser.add_argument("--csv", type=Path, help="optional successful-witness CSV output")
    parser.add_argument("--json", type=Path, help="optional summary JSON output")
    args = parser.parse_args()

    try:
        result = run(args.limit, args.max_k, args.csv)
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
