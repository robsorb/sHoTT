# Inner families

This is a formalization of important feature of (iso-)inner families. In
particular, we provide an interface for dependent composition, crucially needed
for cocartesian families.

We build on
[Buchholtz and Weinberger (2023), Higher Structures 7, §4](https://doi.org/10.21136/HS.2023.04).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

## Inner families

```rzk
#def is-inner-family
  (B : U)
  (E : B -> U)
  : U
  := is-right-orthogonal-family
    (2 * 2)
    Δ²
    Λ²₁
    B
    E
```

## Iso-Inner families

```rzk
#def is-isoinner-family
  (B : U)
  (E : B -> U)
  : U
  := product
    (is-inner-family B E)
    ((b : B) -> is-rezk (E b))

```
