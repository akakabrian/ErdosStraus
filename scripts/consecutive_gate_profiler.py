#!/usr/bin/env python3
"""Exact consecutive-offset profiler for Erdős--Straus residual primes.

For each prime p congruent to 1 modulo 24, write

    m = (p + 3) / 4,  x_k = m + k,  d_k = 4*k + 3.

The script compares:

1. the existing Type-II divisor-square gate;
2. the complete two-unit-fraction factorization after fixing 1/x_k;
3. the unbounded unit Type-I gate d_k | p+1.

Every emitted witness is verified by exact integer arithmetic and strict
denominator inequalities. Finite output is discovery evidence, not a proof of
universal coverage.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Iterator


@dataclass(frozen=True)
class TwoFractionWitness:
    p: int
    k: int
    x: int
    d: int
    p_exponent_in_u: int
    q: int
    u: int
    v: int
    y: int
    z: int
    certificate_kind: str
    normalized_parameters: dict[str, int] | None


@dataclass(frozen=True)
class UnitTypeIWitness:
    p: int
    divisor_d: int
    k: int
    x: int
    s: int
    y: int
    z: int


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


def small_primes(limit: int) -> list[int]:
    sieve = prime_sieve(limit)
    return [n for n in range(2, limit + 1) if sieve[n]]


def residual_primes(limit: int) -> Iterator[int]:
    sieve = prime_sieve(limit)
    for p in range(73, limit + 1, 24):
        if sieve[p]:
            yield p


def factorize(n: int, primes: Iterable[int]) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("factorization requires n >= 1")
    result: list[tuple[int, int]] = []
    remaining = n
    for prime in primes:
        if prime * prime > remaining:
            break
        if remaining % prime == 0:
            exponent = 0
            while remaining % prime == 0:
                remaining //= prime
                exponent += 1
            result.append((prime, exponent))
        if remaining == 1:
            break
    if remaining > 1:
        result.append((remaining, 1))
    return result


def divisors_of_square(factors: list[tuple[int, int]]) -> list[int]:
    divisors = [1]
    for prime, exponent in factors:
        powers = [prime**e for e in range(2 * exponent + 1)]
        divisors = [divisor * power for divisor in divisors for power in powers]
    return sorted(divisors)


def verify_strict_certificate(p: int, x: int, y: int, z: int) -> None:
    if not (1 <= x < y < z):
        raise AssertionError("strict denominator order failed")
    if 4 * x * y * z != p * (x * y + x * z + y * z):
        raise AssertionError("polynomial Erdős--Straus identity failed")


def normalize_type_i(
    p: int, k: int, x: int, d: int, q: int
) -> dict[str, int]:
    g = math.gcd(x, q)
    a = q // g
    b = x // g
    if math.gcd(a, b) != 1 or g % a != 0:
        raise AssertionError("Type-I gcd normalization failed")
    c = g // a
    if q != a * a * c or x != a * b * c:
        raise AssertionError("Type-I product normalization failed")
    if (a + p * b) % d != 0:
        raise AssertionError("Type-I residue cancellation failed")
    s = (a + p * b) // d
    if not (a < p * b and b < s):
        raise AssertionError("Type-I strict factor inequalities failed")
    return {"a": a, "b": b, "c": c, "s": s}


def normalize_type_ii(
    p: int, k: int, x: int, d: int, q: int
) -> dict[str, int]:
    g = math.gcd(x, q)
    a = q // g
    b = x // g
    if math.gcd(a, b) != 1 or g % a != 0:
        raise AssertionError("Type-II gcd normalization failed")
    c = g // a
    if q != a * a * c or x != a * b * c:
        raise AssertionError("Type-II product normalization failed")
    if (a + b) % d != 0:
        raise AssertionError("Type-II residue cancellation failed")
    s = (a + b) // d
    if not (a < b < p * s):
        raise AssertionError("Type-II strict factor inequalities failed")
    return {"a": a, "b": b, "c": c, "s": s}


def two_fraction_witness_at_offset(
    p: int,
    k: int,
    trial_primes: list[int],
) -> TwoFractionWitness | None:
    x = (p + 3) // 4 + k
    d = 4 * k + 3
    if d >= p:
        return None
    factors = factorize(x, trial_primes)
    divisors = divisors_of_square(factors)
    px = p * x
    square = px * px
    candidates: list[tuple[int, int, int]] = []

    # If u*v=(p*x)^2 and u<p*x, the p-adic exponent in u is 0, 1, or 2.
    for p_exponent in (0, 1, 2):
        p_power = p**p_exponent
        upper_q = (px - 1) // p_power
        for q in divisors:
            if q > upper_q:
                break
            u = p_power * q
            if (u + px) % d == 0:
                candidates.append((u, p_exponent, q))

    if not candidates:
        return None

    u, p_exponent, q = min(candidates)
    v = square // u
    y = (u + px) // d
    z = (v + px) // d
    if u * v != square or not (u < px < v):
        raise AssertionError("two-fraction factorization failed")
    verify_strict_certificate(p, x, y, z)

    normalized: dict[str, int] | None
    if p_exponent == 0:
        kind = "Type-I"
        normalized = normalize_type_i(p, k, x, d, q)
    elif p_exponent == 1:
        kind = "Type-II"
        normalized = normalize_type_ii(p, k, x, d, q)
    else:
        kind = "Type-I-dual"
        normalized = None

    return TwoFractionWitness(
        p=p,
        k=k,
        x=x,
        d=d,
        p_exponent_in_u=p_exponent,
        q=q,
        u=u,
        v=v,
        y=y,
        z=z,
        certificate_kind=kind,
        normalized_parameters=normalized,
    )


def first_complete_witness(
    p: int,
    max_k: int,
    trial_primes: list[int],
) -> TwoFractionWitness | None:
    for k in range(max_k + 1):
        witness = two_fraction_witness_at_offset(p, k, trial_primes)
        if witness is not None:
            return witness
    return None


def first_type_ii_offset(
    p: int,
    max_k: int,
    trial_primes: list[int],
) -> int | None:
    for k in range(max_k + 1):
        x = (p + 3) // 4 + k
        d = 4 * k + 3
        if d >= p:
            break
        factors = factorize(x, trial_primes)
        for q in divisors_of_square(factors):
            if q >= x:
                break
            if (q + x) % d == 0:
                return k
    return None


def unit_type_i_witness(
    p: int,
    trial_primes: list[int],
) -> UnitTypeIWitness | None:
    factors = factorize(p + 1, trial_primes)
    eligible = [prime for prime, _ in factors if prime % 4 == 3]
    if not eligible:
        return None
    d = min(eligible)
    if not (0 < d < p and (d - 3) % 4 == 0):
        raise AssertionError("unit Type-I offset conditions failed")
    k = (d - 3) // 4
    x = (p + d) // 4
    s = (p + 1) // d
    y = x * s
    z = p * x * s
    if p + d != 4 * x or p + 1 != d * s:
        raise AssertionError("unit Type-I equations failed")
    verify_strict_certificate(p, x, y, z)
    return UnitTypeIWitness(p=p, divisor_d=d, k=k, x=x, s=s, y=y, z=z)


def counter_to_json(counter: Counter[int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def run(limit: int, max_k: int) -> dict[str, object]:
    if limit < 73:
        raise ValueError("limit must be at least 73")
    if max_k < 0:
        raise ValueError("max-k must be nonnegative")

    max_x = (limit + 3) // 4 + max_k
    trial_primes = small_primes(math.isqrt(max(limit + 1, max_x)) + 1)

    checked = 0
    type_ii_distribution: Counter[int] = Counter()
    complete_distribution: Counter[int] = Counter()
    p_exponent_distribution: Counter[int] = Counter()
    type_ii_unresolved: list[int] = []
    complete_unresolved: list[int] = []
    improved: list[dict[str, object]] = []
    unit_hits = 0
    unit_misses = 0
    unit_record: UnitTypeIWitness | None = None

    for p in residual_primes(limit):
        checked += 1
        type_ii_k = first_type_ii_offset(p, max_k, trial_primes)
        complete = first_complete_witness(p, max_k, trial_primes)
        unit = unit_type_i_witness(p, trial_primes)

        if type_ii_k is None:
            type_ii_unresolved.append(p)
        else:
            type_ii_distribution[type_ii_k] += 1

        if complete is None:
            complete_unresolved.append(p)
        else:
            complete_distribution[complete.k] += 1
            p_exponent_distribution[complete.p_exponent_in_u] += 1

        if (
            type_ii_k is not None
            and complete is not None
            and complete.k < type_ii_k
        ):
            improved.append(
                {
                    "p": p,
                    "type_ii_first_k": type_ii_k,
                    "complete_first_k": complete.k,
                    "offset_improvement": type_ii_k - complete.k,
                    "witness": asdict(complete),
                }
            )

        if unit is None:
            unit_misses += 1
        else:
            unit_hits += 1
            if unit_record is None or (unit.k, unit.p) > (unit_record.k, unit_record.p):
                unit_record = unit

    improvement_record = (
        max(improved, key=lambda row: (row["offset_improvement"], row["p"]))
        if improved
        else None
    )

    return {
        "scope": "finite exact computation; not a universal proof",
        "sequence": {
            "m": "(p+3)/4",
            "x_k": "m+k",
            "d_k": "4*k+3",
        },
        "limit": limit,
        "max_k_for_bounded_searches": max_k,
        "residual_primes_checked": checked,
        "type_ii_only": {
            "first_offset_distribution": counter_to_json(type_ii_distribution),
            "largest_first_k": max(type_ii_distribution, default=None),
            "unresolved_count": len(type_ii_unresolved),
            "unresolved_primes": type_ii_unresolved,
        },
        "complete_two_fraction_factorization": {
            "first_offset_distribution": counter_to_json(complete_distribution),
            "selected_p_exponent_in_u": counter_to_json(p_exponent_distribution),
            "largest_first_k": max(complete_distribution, default=None),
            "unresolved_count": len(complete_unresolved),
            "unresolved_primes": complete_unresolved,
            "strictly_earlier_than_type_ii_count": len(improved),
            "largest_offset_improvement": (
                improvement_record["offset_improvement"] if improvement_record else None
            ),
            "improvement_record": improvement_record,
        },
        "unit_type_i_gate_from_p_plus_one": {
            "criterion": "an odd prime divisor d of p+1 with d congruent to 3 modulo 4",
            "covered_count": unit_hits,
            "not_covered_count": unit_misses,
            "covered_fraction": unit_hits / checked,
            "largest_required_k": unit_record.k if unit_record else None,
            "largest_required_k_witness": asdict(unit_record) if unit_record else None,
        },
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
