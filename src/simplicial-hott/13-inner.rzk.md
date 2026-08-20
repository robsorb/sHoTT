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

## Dependent homs over arrows

```rzk

#def dhom-arr
  ( B : U)
  ( f : Δ¹ → B)
  ( E : B → U)
  ( x : E(f 0₂))
  ( y : E(f 1₂))
  : U
  := dhom B (f 0₂) (f 1₂) f E x y

```

## Edges of triangles in types

```rzk

#section edges-of-triangles

#variable B : U

#def fst-Δ² (a : Δ² → B)
  : Δ¹ → B
  := \ t → a (t , 0₂)

#def snd-Δ² (a : Δ² → B)
  : Δ¹ → B
  := \ t → a (1₂ , t)

#def comp-Δ² (a : Δ² → B)
  : Δ¹ → B
  := \ t → a (t , t)


#def hor-edge-Δ²
  ( a : Δ² → B)
  ( y : Δ¹)
  : hom B (a (y , y)) (a (1₂ , y))
  := \ x → recOR (x ≤ y ↦ a (y , y) , y ≤ x ↦ a (x , y))


#variable E
  : B → U

#def fst-dΔ² (a : Δ² → B) (da : (t : Δ²) → E (a t))
  : ( t : Δ¹) → E (fst-Δ² a t)
  := \ t → da (t , 0₂)

#def snd-dΔ² (a : Δ² → B) (da : (t : Δ²) → E (a t))
  : ( t : Δ¹) → E (snd-Δ² a t)
  := \ t → da (1₂ , t)

#def comp-dΔ² (a : Δ² → B) (da : (t : Δ²) → E (a t))
  : ( t : Δ¹) → E (comp-Δ² a t)
  := \ t → da (t , t)

#end edges-of-triangles
```

## Triangles with fixed boundaries

```rzk

#def dtriangle-with-horn
  ( B : U)
  ( σ : Δ² → B)
  ( E : B → U)
  ( x : E(σ (0₂ , 0₂)))
  ( y : E(σ (1₂ , 0₂)))
  ( z : E(σ (1₂ , 1₂)))
  ( f : dhom-arr B (fst-Δ² B σ) E x y)
  ( g : dhom-arr B (snd-Δ² B σ) E y z)
  : U
  := ((s , t) : Δ²) → E (σ (s , t)) [
    t ≡ 0₂ ↦ f s
  , s ≡ 1₂ ↦ g t
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
#variable σ : Δ² → B

#def fill-over-is-inner-family
  ( x : E(σ (0₂ , 0₂)))
  ( y : E(σ (1₂ , 0₂)))
  ( z : E(σ (1₂ , 1₂)))
  ( f : dhom-arr B (fst-Δ² B σ) E x y)
  ( g : dhom-arr B (snd-Δ² B σ) E y z)
  : dtriangle-with-horn B σ E x y z f g
  := extend-section-is-right-orthogonal-family
      ( 2 × 2) Δ² Λ²₁ B E is-inner-E σ
      ( \ (s , t) →
        recOR (
          t ≡ 0₂ ↦ f s
        , s ≡ 1₂ ↦ g t
        ))

#def comp-over-is-inner-family uses (is-inner-E)
  ( x : E(σ (0₂ , 0₂)))
  ( y : E(σ (1₂ , 0₂)))
  ( z : E(σ (1₂ , 1₂)))
  :
  ( dhom-arr B (fst-Δ² B σ) E x y) → (dhom-arr B (snd-Δ² B σ) E y z)
  → dhom-arr B (comp-Δ² B σ) E x z
  := \ f g t → fill-over-is-inner-family x y z f g (t , t)

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
