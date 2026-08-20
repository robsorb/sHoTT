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




## Dependent arrows
```rzk

#def darr
  ( B : U)
  ( f : Δ¹ → B)
  ( E : B → U)
  : U
  := (t : Δ¹) → E (f t)

#def darr-from
  ( B : U)
  ( f : Δ¹ → B)
  ( E : B → U)
  ( e : E(f 0₂))
  : U
  := (t : Δ¹) → E (f t) [t ≡ 0₂ ↦ e]

```

## Triangles with fixed spine

```rzk

#def dtriangle-with-horn
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : U
  := ((s , t) : Δ²) → E (σ (s , t)) [
    t ≡ 0₂ ↦ f' s
  , s ≡ 1₂ ↦ g' t
  ]

```


## Inner families

```rzk
#def is-inner-family
  ( B : U)
  ( E : B → U)
  : U
  := is-right-orthogonal-family
    ( 2 × 2)
    Δ²
    Λ²₁
    B
    E
```

### The relative composition map for morphisms with a fixed domain

```rzk

#section composition-is-inner-family

#variable B : U
#variable E : B → U
#variable is-inner-E : is-inner-family B E
#variables x y z : B
#variable f : hom B x y
#variable g : hom B  y z
#variable h : hom B  x z
#variable σ : hom2 B x y z f g h

#def fill-over-is-inner-family
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : dtriangle-with-horn B x y z f g h σ E x' y' z' f' g'
  := extend-section-is-right-orthogonal-family
      ( 2 × 2) Δ² Λ²₁ B E is-inner-E σ
      ( \ (s , t) →
        recOR (
          t ≡ 0₂ ↦ f' s
        , s ≡ 1₂ ↦ g' t
        ))

#def comp-over-is-inner-family uses (is-inner-E σ)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  :
  ( dhom B x y f E x' y')
  → ( dhom B y z g E y' z')
  → ( dhom B x z h E x' z')
  := \ f' g' t → fill-over-is-inner-family x' y' z' f' g' (t , t)

#end composition-is-inner-family

```


## Iso-Inner families

```rzk
#def is-isoinner-family
  ( B : U)
  ( E : B → U)
  : U
  := product
    ( is-inner-family B E)
    ( ( b : B) → is-rezk (E b))

```
