# Audit of Ionascu–Wilson's modulo-9240 formulas

## Bibliographic source

Eugen J. Ionascu and Andrew Wilson, *On the Erdős–Straus Conjecture*, arXiv:1001.1100, 7 January 2010; later published in *Revue Roumaine de Mathématiques Pures et Appliquées* 56(1), 21–30.

Source: https://arxiv.org/abs/1001.1100

## What the paper proves

The paper extends Mordell's congruence reduction. Its Theorem 2.1 leaves twelve candidate prime classes modulo 1320, and Theorem 2.2 combines those with the earlier modulo-168 reduction and two additional polynomial families to leave 34 classes modulo 9240.

The modulo-1320 exceptional set is:

```text
{1,49,169,289,361,529,721,841,889,961,1081,1201}.
```

Intersecting this set with the three surviving classes modulo 168 gives 36 classes modulo 9240. The two displayed families for `1201 mod 9240` and `6001 mod 9240` remove two of them, leaving the stated 34.

## Printed formula for `9240t+1201`

The inspected arXiv PDF displays an identity whose two large denominators contain the factor

```text
9240t+1
```

rather than

```text
9240t+1201.
```

Read literally, the displayed formula is:

```text
4/(9240t+1201)
 = 1/(2310t+308)
 + 1/[5(9240t+1)(15t+2)]
 + 1/[770(9240t+1)(15t+2)].
```

Exact symbolic cross-multiplication shows that this printed identity is false. This is not a numerical-rounding issue.

## Exact correction

Replacing both occurrences of `9240t+1` by `9240t+1201` gives the exact identity

```text
4/(9240t+1201)
 = 1/(2310t+308)
 + 1/[5(9240t+1201)(15t+2)]
 + 1/[770(9240t+1201)(15t+2)].
```

It is a direct Type-II factor-pair certificate with

```text
p = 9240t+1201
d = 31
a = 1
b = 154
c = 15t+2
s = 5.
```

Indeed,

```text
a+b = 155 = 31*5 = d*s,
p+d = 9240t+1232 = 4*154*(15t+2) = 4abc.
```

The three denominators are

```text
abc  = 154(15t+2) = 2310t+308,
pacs = 5(9240t+1201)(15t+2),
pbcs = 770(9240t+1201)(15t+2).
```

They are strictly ordered for every `t≥0`. This corrected family is formalized in `ModElevenFamilies.lean` on the branch `erdos-242-mod-eleven-reduction`.

## Formula for `9240t+6001`

The paper's second displayed identity is exact:

```text
4/(9240t+6001)
 = 1/[770(3t+2)]
 + 1/[385(9240t+6001)(2034t+1321)]
 + 1/[22(3t+2)(2034t+1321)].
```

For the strict-order target, the final two terms are reordered. The denominators used formally are:

```text
770(3t+2),
22(3t+2)(2034t+1321),
385(9240t+6001)(2034t+1321).
```

Exact polynomial expansion verifies both the identity and strict ordering.

## Resulting 34 classes

The 36 CRT intersections are:

```text
1,169,289,361,529,841,961,1201,1369,1681,1849,2041,
2209,2521,2641,2689,2809,3361,3481,3529,3721,4321,
4489,5041,5161,5329,5569,6001,6169,6241,6889,7561,
7681,7921,8089,8761.
```

Removing `1201` and `6001` with the two exact families leaves:

```text
1,169,289,361,529,841,961,1369,1681,1849,2041,2209,
2521,2641,2689,2809,3361,3481,3529,3721,4321,4489,
5041,5161,5329,5569,6169,6241,6889,7561,7681,7921,
8089,8761.
```

## Integrity conclusion

The typographical error does not invalidate the paper's stated 34-class theorem because a simple exact correction supplies the intended family. However, the printed identity itself must not be copied or formalized unchanged. Our project records the discrepancy, proves the corrected identity independently, and preserves the exact strict-denominator target.
