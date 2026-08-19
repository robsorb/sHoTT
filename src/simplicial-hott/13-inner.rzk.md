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

#def comp-over-is-inner-family
  ( B : U)
  ( E : B → U)
  ( is-inner-E : is-inner-family B E)
  ( σ : Δ² → B)
  ( f : darr B (fst-Δ² B σ) E)
  ( g : darr-from B (snd-Δ² B σ) E (f 1₂))
  : dhom B (σ (0₂ , 0₂)) (σ (1₂ , 1₂)) (comp-Δ² B σ) E (f 0₂) (g 1₂)
  := \ t →
    extend-section-is-right-orthogonal-family
      ( 2 × 2) Δ² Λ²₁ B E is-inner-E σ
      ( \ (x , y) →
        recOR (
          y ≡ 0₂ ↦ f x
        , x ≡ 1₂ ↦ g y
        ))
      ( t , t)

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
