# Simultaneous unit-gate failure profile through `10^8`

## Scope

This is finite exact computation, not a universal proof.

The run restricts to residual primes for which the unit Type-I `p+1` gate fails and then searches the complete two-fraction factorization along the consecutive offsets.

## Reproduction

```bash
python scripts/simultaneous_failure_profiler.py \
  --limit 100000000 \
  --max-k 40 \
  --json data/simultaneous-failure-summary-100m.json
```

## Result

```text
residual primes checked:                         719781
unit-gate successes:                             398283
unit-gate failures:                              321498
unresolved among unit-gate failures through k=40:     0
largest first complete offset after unit failure:    26
```

The exact record is

```text
p=8803369,
p+1=2*5*880337,
first complete witness k=26,
d=107,
q=121,
a=1,
b=18189,
c=121,
s=170.
```

This falsifies the combined fixed-bound candidate `k≤25`. The candidate `k≤10` is already falsified by

```text
p=496609,
p+1=2*5*53*937,
first complete witness k=12.
```

No observed case beyond `k=26` is not a theorem that `k≤26` universally.

## Integrity hashes

```text
scripts/simultaneous_failure_profiler.py
c4c883fae681483a522480b16563a8e44cf7a6004de0e6a99413f6cb29eda516

data/simultaneous-failure-summary-100m.json
99c2fe58e4cbb5dd3ad9038081108ae0a0fd7d1c67eaae0de967e0f39a21c9b9
```
