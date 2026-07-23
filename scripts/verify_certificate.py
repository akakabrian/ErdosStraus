#!/usr/bin/env python3
"""Verify an Erdős–Straus Type-II factor-pair certificate using exact arithmetic."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class TypeIICertificate:
    p: int
    a: int
    b: int
    c: int
    s: int
    d: int

    @property
    def denominators(self) -> tuple[int, int, int]:
        return (
            self.a * self.b * self.c,
            self.p * self.a * self.c * self.s,
            self.p * self.b * self.c * self.s,
        )

    def verify(self) -> dict[str, Any]:
        x, y, z = self.denominators
        positive_parameters = all(v > 0 for v in (self.p, self.a, self.b, self.c, self.s, self.d))
        factor_pair_equation = self.p + self.d == 4 * self.a * self.b * self.c
        residue_equation = self.a + self.b == self.d * self.s
        parameter_order = self.a < self.b < self.p * self.s
        denominator_order = 1 <= x < y < z
        polynomial_identity = 4 * x * y * z == self.p * (x * y + x * z + y * z)
        rational_identity = Fraction(4, self.p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
        valid = all(
            (
                positive_parameters,
                factor_pair_equation,
                residue_equation,
                parameter_order,
                denominator_order,
                polynomial_identity,
                rational_identity,
            )
        )
        return {
            "valid": valid,
            "positive_parameters": positive_parameters,
            "factor_pair_equation": factor_pair_equation,
            "residue_equation": residue_equation,
            "parameter_order": parameter_order,
            "denominator_order": denominator_order,
            "polynomial_identity": polynomial_identity,
            "rational_identity": rational_identity,
            "denominators": [x, y, z],
        }


def load_certificate(path: Path) -> TypeIICertificate:
    payload = json.loads(path.read_text(encoding="utf-8"))
    try:
        return TypeIICertificate(**{key: int(payload[key]) for key in ("p", "a", "b", "c", "s", "d")})
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError(f"invalid certificate JSON: {exc}") from exc


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path, help="JSON file containing p,a,b,c,s,d")
    args = parser.parse_args()

    try:
        certificate = load_certificate(args.certificate)
        result = certificate.verify()
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        parser.error(str(exc))

    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
