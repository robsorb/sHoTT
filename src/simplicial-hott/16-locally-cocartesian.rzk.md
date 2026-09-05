# Coherently locally cocartesian families


```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Locally cocartesian arrows

```rzk
#def is-locally-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
  ( e'' : P b')
  → is-cocartesian-arrow-over
    B b b' b' u (id-hom B b') u (comp-id-witness B b b' u)
    P e e' e'' f
```

### An arrow is locally cocartesian if and only if post-composition is an equivalence

```rzk

#def is-locally-cocartesian-arrow-is-equiv-comp-over-is-inner-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : ( ( e'' : P b')
  → is-equiv
      ( hom (P b') e' e'')
      ( dhom B b b' u P e e'')
      ( comp-over-is-inner-family B P is-inner-P
        b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f))
  → is-locally-cocartesian-arrow B b b' u P e e' f
  :=
  \ is-equiv-comp e'' →
    is-cocartesian-arrow-over-is-equiv-comp-over-is-inner B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f
      ( is-equiv-comp e'')

#def is-equiv-comp-over-is-inner-locally-cocartesian-arrow-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : is-locally-cocartesian-arrow B b b' u P e e' f
  → ( e'' : P b') → is-equiv
    ( hom (P b') e' e'')
    ( dhom B b b' u P e e'')
    ( comp-over-is-inner-family B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f)
  :=
  \ is-locally-cocart-f e'' →
    is-equiv-comp-over-is-inner-is-cocartesian-arrow-over B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f
      ( is-locally-cocart-f e'')

#def equiv-hom-dhom-is-locally-cocartesian-arrow-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  ( is-locally-cocart-f : is-locally-cocartesian-arrow B b b' u P e e' f)
  : ( e'' : P b')
  → Equiv (hom (P b') e' e'') (dhom B b b' u P e e'')
  :=
  \ e'' →
    ( comp-over-is-inner-family B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f
    , is-equiv-comp-over-is-inner-locally-cocartesian-arrow-is-inner
      B P is-inner-P
      b b' u e e' f is-locally-cocart-f
      e'')

```

## Coherently locally cocartesian family

A family is coherently locally cocartesian if it is isoinner and any arrow in
the base has a locally cocartesian lift, given a point in the fiber over
the domain. The reason for the prefix 'coherently' here is that these lifts are
required to exist functorialy in the base, which is not the case for the
classical notion of locally cocartesian fibrations.

```rzk
#def has-locally-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → (b' : B) → (u : hom B b b')
    → ( e : P b) → (Σ (e' : P b')
      , ( Σ ( f : dhom B b b' u P e e') , is-locally-cocartesian-arrow B b b' u
          P e e' f))
```

```rzk
#def is-coherently-locally-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-isoinner-family B P) (has-locally-cocartesian-lifts B P)
```

## Coherently locally cocartesian families have a coherent action

```rzk

#section coherent-action-locally-cocartesian

#variable B : U
#variable E : B → U
#variable is-coherently-locally-cocartesian-family-E :
  is-coherently-locally-cocartesian-family B E
```

### The action

The action induced by being a coherently locally cocartesian family.

```rzk
#def action-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  : E x → E y
  :=
  \ e → first (second
    ( is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f) (e))
```

### The chosen locally cocartesian lifts

```rzk
#def lift-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom B x y f E e (action-coherently-locally-cocartesian x y f e)
  :=
  first (second (second
    ( is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f) (e)))

#def is-locally-cocartesian-lift-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : is-locally-cocartesian-arrow B x y f E
    e
    ( action-coherently-locally-cocartesian x y f e)
    ( lift-coherently-locally-cocartesian x y f e)
  :=
  second (second (second
    ( is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f) (e)))
```

### Unitality

This action is unital.

```rzk

#def is-unital-action-coherently-locally-cocartesian
  ( x : B)
  ( e : E x)
  : action-coherently-locally-cocartesian x x (id-hom B x) e = e
  :=
  rev
    ( E x)
    ( e)
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( eq-representable-isomorphism funext extext
      ( E x)
      ( rezk-fiber-is-isoinner-family B E
        ( first is-coherently-locally-cocartesian-family-E) x)
      ( action-coherently-locally-cocartesian x x (id-hom B x) e)
      ( e)
      ( equiv-hom-dhom-is-locally-cocartesian-arrow-is-inner B E
        ( is-inner-family-is-iso-inner-family B E
          ( first is-coherently-locally-cocartesian-family-E))
        x x (id-hom B x)
        ( e)
        ( action-coherently-locally-cocartesian x x (id-hom B x) e)
        ( lift-coherently-locally-cocartesian x x (id-hom B x) e)
        ( is-locally-cocartesian-lift-coherently-locally-cocartesian
          x x (id-hom B x) e)))

```



```rzk
#end coherent-action-locally-cocartesian
```



## Coherently locally cocartesian families are cocartesian
