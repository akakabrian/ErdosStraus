#!/usr/bin/env python3
"""Exact d=11 opposite-divisor automaton on prime-power components.

For x = product_i q_i^e_i, coprime divisors a,b correspond to assigning each
full prime-power component q_i^e_i to A, B, or neither. This script tracks the
resulting residue pair (a mod 11,b mod 11) exactly. It does not approximate by
prime support and it does not claim universal coverage.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path
from typing import Sequence

import pandas as pd
from sympy import factorint

MODULUS = 11
UNITS = frozenset(range(1, MODULUS))


def component_residues(x: int) -> tuple[int, ...]:
    """Residues q^e mod 11 for the pairwise-coprime prime-power components of x."""
    return tuple(sorted(pow(int(q), int(e), MODULUS) for q, e in factorint(x).items()))


def has_opposite_assignment(residues: Sequence[int]) -> bool:
    """Decide whether disjoint nonempty component sets multiply to opposite residues."""
    states: set[tuple[int, int, bool, bool]] = {(1, 1, False, False)}
    for residue in residues:
        next_states = set(states)
        for a, b, used_a, used_b in states:
            next_states.add(((a * residue) % MODULUS, b, True, used_b))
            next_states.add((a, (b * residue) % MODULUS, used_a, True))
        states = next_states
    return any(
        used_a and used_b and (a + b) % MODULUS == 0
        for a, b, used_a, used_b in states
    )


def minimal_success_patterns(max_components: int) -> list[tuple[int, ...]]:
    """Enumerate inclusion-minimal residue multisets forcing the d=11 gate."""
    minimal: list[tuple[int, ...]] = []
    for size in range(2, max_components + 1):
        for pattern in combinations_with_replacement(range(1, MODULUS), size):
            if not has_opposite_assignment(pattern):
                continue
            counts = Counter(pattern)
            if any(
                all(Counter(old)[r] <= counts[r] for r in Counter(old))
                for old in minimal
            ):
                continue
            minimal.append(pattern)
    return minimal


def multiplicatively_closed(subset: frozenset[int]) -> bool:
    """Check closure under multiplication modulo 11."""
    return all((a * b) % MODULUS in subset for a in subset for b in subset)


def opposite_free(subset: frozenset[int]) -> bool:
    """Check that the subset contains no pair summing to zero modulo 11."""
    return all((-a) % MODULUS not in subset for a in subset)


def maximal_closed_opposite_free_sets() -> list[frozenset[int]]:
    """Enumerate maximal support-only obstruction sets in (Z/11Z)^*."""
    candidates: list[frozenset[int]] = []
    ordered_units = sorted(UNITS - {1})
    for mask in range(1 << len(ordered_units)):
        subset = frozenset(
            {1}
            | {
                residue
                for index, residue in enumerate(ordered_units)
                if mask & (1 << index)
            }
        )
        if multiplicatively_closed(subset) and opposite_free(subset):
            candidates.append(subset)
    return [
        subset
        for subset in candidates
        if not any(subset < other for other in candidates)
    ]


def profile_csv(input_csv: Path, output_csv: Path | None) -> pd.DataFrame:
    """Profile residual-prime rows whose first witness occurs after d=11."""
    frame = pd.read_csv(input_csv, usecols=["p", "k", "d"])
    survivors = frame[frame["k"] >= 3].copy()
    survivors["x11"] = (survivors["p"] + 11) // 4
    survivors["component_residues_mod11"] = survivors["x11"].map(component_residues)
    survivors["d11_gate"] = survivors["component_residues_mod11"].map(
        has_opposite_assignment
    )
    if output_csv is not None:
        survivors.to_csv(output_csv, index=False)
    return survivors


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input-csv", type=Path)
    parser.add_argument("--output-csv", type=Path)
    parser.add_argument("--max-components", type=int, default=4)
    args = parser.parse_args()

    maximal_sets = maximal_closed_opposite_free_sets()
    print("maximal multiplicatively closed opposite-free support sets:")
    for subset in maximal_sets:
        print(tuple(sorted(subset)))

    patterns = minimal_success_patterns(args.max_components)
    print(
        f"minimal success patterns through {args.max_components} components: "
        f"{len(patterns)}"
    )
    for pattern in patterns:
        print(pattern)

    if args.input_csv:
        survivors = profile_csv(args.input_csv, args.output_csv)
        failures = int((~survivors["d11_gate"]).sum())
        print(f"rows surviving through d=11: {len(survivors)}")
        print(f"exact d=11 failures among those rows: {failures}")
        print(f"exact d=11 successes among those rows: {len(survivors) - failures}")


if __name__ == "__main__":
    main()
