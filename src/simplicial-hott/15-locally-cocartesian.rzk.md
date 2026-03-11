# "Locally" cocartesian families



This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#def degen-Δ²-vertical
  ( B : U)
  ( f : Δ¹ → B)
  : Δ² → B
  := \ (x , y) → f x
```


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
    → ( h : dhom B b b' u P e e'')
    → is-contr
        ( Σ ( g : hom (P b') e' e'')
        , ( dhom2 B b b' b' u (id-hom B b') u (degen-Δ²-vertical B u) P e e' e'' f g h))



#def fill-locally-cocartesian-arrow
  ( B : U)
  ( E : B → U)
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  ( g : darr-from B E b (f 0₂))
  : is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) (f)
  → hom (E (b 1₂)) (f 1₂) (g 1₂)
  := \ is-locally-cocart →
    first (first (is-locally-cocart (g 1₂) (\ t → g t)))
```


```rzk
#def locally-cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ ( e' : P b')
    , Σ ( f : dhom B b b' u P e e') , is-locally-cocartesian-arrow B b b' u P e e' f
```


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

## Arrows are locally cocartesian whenever precomposition is an equivalence.

```rzk

#section is-equiv-composition

#variable B : U
#variable E : B → U
#variable E-inner : is-inner B E

#def is-locally-cocartesian-arrow-is-equiv-comp-over-Inner
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  : is-equiv
      ( arr-from (E (b 1₂)) (f 1₂))
      ( darr-from B E b (f 0₂))
      ( comp-over-Inner B E E-inner (degen-Δ²-vertical B b) f)
  → is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) f
  := \ is-equiv-comp e'' h →
    is-contr-equiv-is-contr
      ( fib
        ( arr-from (E (b 1₂)) (f 1₂))
        ( darr-from B E b (f 0₂))
        ( comp-over-Inner B E E-inner (degen-Δ²-vertical B b) f)
        ( h))
      ( ( Σ ( g : hom (E (b 1₂)) (f 1₂) e'')
        , ( dhom2 B (b 0₂) (b 1₂) (b 1₂) b (id-hom B (b 1₂)) b (degen-Δ²-vertical B b)
          E (f 0₂) (f 1₂) e'' f g h)))
      ( equiv-fib-comp-dtriangles-Inner B E E-inner (degen-Δ²-vertical B b) f h)
      ( is-contr-map-is-equiv
        ( arr-from (E (b 1₂)) (f 1₂))
        ( darr-from B E b (f 0₂))
        ( comp-over-Inner B E E-inner (degen-Δ²-vertical B b) f)
        ( is-equiv-comp)
        ( h))


#end is-equiv-composition

```


```rzk

#variable B : U
#variable E : B → U
#variable lifts : has-locally-cocartesian-lifts B E
-- #variable E-inner : is-inner B E


#def action-locally-cocartesian
  : ( f : Δ¹ → B) → E (f 0₂) → E (f 1₂)
  := \ f e → first (lifts (f 0₂) (f 1₂) f e)

#def hom-action-id-id-locally-cocartesian
  ( b : B) (e : E b)
  : hom (E b) (action-locally-cocartesian (id-hom B b) e) (e)
  := fill-locally-cocartesian-arrow B E (id-hom B b)
    ( first (second (lifts b b (id-hom B b) e)))
    ( \ t → e)
    ( second (second (lifts b b (id-hom B b) e)))

#def hom-id-action-id-locally-cocartesian
  ( b : B) (e : E b)
  : hom (E b) (e) (action-locally-cocartesian (id-hom B b) e)
  := first (second (lifts (b) (b) (id-hom B b) e))

```
