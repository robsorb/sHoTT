# Cocartesian families

These formalizations capture cocartesian families as treated in
[Buchholtz and Weinberger (2023), Higher Structures 7](https://doi.org/10.21136/HS.2023.04).

The goal, for now, is not to give a general structural account as in the paper
but rather to provide the definitions and results that are necessary to prove
the cocartesian Yoneda Lemma.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `03-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `04-extension-types.rzk.md` — We use the fubini theorem and extension
  extensionality.
- `05-segal-types.rzk.md` - We make heavy use of the notion of Segal types
- `10-rezk-types.rzk.md`- We use Rezk types.
- `12-inner.rzk.md` - We use (iso)inner families.

## Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"
#def is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
    ( b'' : B) → (v : hom B b' b'') → (w : hom B b b'')
    → ( sigma : hom2 B b b' b'' u v w) → (e'' : P b'')
    → ( h : dhom B b b'' w P e e'')
    → is-contr
        ( Σ ( g : dhom B b' b'' v P e' e'')
        , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
```

## Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ ( e' : P b')
    , Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f
```

## Cocartesian family

A family is cocartesian if it is isoinner and any arrow in the has a cocartesian
lift, given a point in the fiber over the domain.

```rzk title="BW23, Definition 5.2.1"
#def has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → (b' : B) → (u : hom B b b')
    → ( e : P b) → (Σ (e' : P b')
      , ( Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u
          P e e' f))
```

```rzk title="BW23, Definition 5.2.2"
#def is-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-isoinner-family B P) (has-cocartesian-lifts B P)
```


## Arrows are cocartesian whenever precomposition is an equivalence.

```rzk

#section is-equiv-composition

#variable B : U
#variable E : B → U
#variable E-inner : is-inner B E

#def is-cocartesian-arrow-is-equiv-comp-over-Inner
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  : ( ( a : ((x , y) : Δ²) → B [y ≡ 0₂ ↦ b x])
  → is-equiv
      ( darr-from B E (snd-Δ² B a) (f 1₂))
      ( darr-from B E (comp-Δ² B a) (f 0₂))
      ( comp-over-Inner B E E-inner a f))
  → is-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) f
  := \ is-equiv-comp →
    \ (b'' : B) → \ (v : hom B (b 1₂) (b'')) → \ (w : hom B (b 0₂) b'') →
    \ (a : hom2 B (b 0₂) (b 1₂) b'' b v w) → \ (e'' : E b'') →
    \ (h : dhom B (b 0₂) b'' w E (f 0₂) e'') →
      is-contr-equiv-is-contr
        ( fib
          ( darr-from B E (snd-Δ² B a) (f 1₂))
          ( darr-from B E (comp-Δ² B a) (f 0₂))
          ( comp-over-Inner B E E-inner a f)
          ( h))
        ( Σ ( g : dhom B (a (1₂ , 0₂)) (a (1₂ , 1₂)) (snd-Δ² B a) E (f 1₂) (h 1₂))
          , dtriangle-with-boundary B E a f g (\ t → h t))
        ( equiv-fib-comp-dtriangles-Inner B E E-inner a f h)
        ( is-contr-map-is-equiv
          ( darr-from B E (snd-Δ² B a) (f 1₂))
          ( darr-from B E (comp-Δ² B a) (f 0₂))
          ( comp-over-Inner B E E-inner a f)
          ( is-equiv-comp a)
          h)

#def has-cocart-lifts-is-equiv-comp-over-Inner
  ( lift : (b : Δ¹ → B) → (e : E (b 0₂)) → darr-from B E b e)
  : ( ( ( a : Δ² → B) → (e : E (a (0₂ , 0₂)))
  → is-equiv
      ( darr-from B E (snd-Δ² B a) (lift (fst-Δ² B a) e 1₂))
      ( darr-from B E (comp-Δ² B a) e)
      ( comp-over-Inner B E E-inner a (lift (fst-Δ² B a) e))))
  → has-cocartesian-lifts B E
  := \ is-equiv-comp → \ (b : B) → \ (b' : B) → \ (u : hom B b b') →
    \ (e : E b) →
      ( lift u e 1₂ , (\ t → lift u e t
      , is-cocartesian-arrow-is-equiv-comp-over-Inner u (lift u e)
        ( \ a →
          is-equiv-comp a e)))

#end is-equiv-composition

```
