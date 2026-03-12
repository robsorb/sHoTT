# "Locally" cocartesian families



This is a literate `rzk` file:

```rzk
#lang rzk-1
```


```rzk
#assume extext
 : ExtExt
```


```rzk
#def degen-Δ²-vertical
  ( B : U)
  ( f : Δ¹ → B)
  : Δ² → B
  := \ (x , y) → f x

#def dhom2-over-arrow
  ( B : U)
  ( b : Δ¹ → B)
  ( E : B → U)
  ( x : E (b 0₂))
  ( y z : E (b 1₂))
  ( f : dhom B (b 0₂) (b 1₂) b E x y)
  ( g : hom (E (b 1₂)) y z)
  ( h : dhom B (b 0₂) (b 1₂) b E x z)
  : U
  := dhom2 B (b 0₂) (b 1₂) (b 1₂) b (id-hom B (b 1₂)) b (degen-Δ²-vertical B b)
    E x y z f g h

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
        , ( dhom2-over-arrow B u P e e' e'' f g h))



#def hom-fill-locally-cocartesian-arrow
  ( B : U)
  ( E : B → U)
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  ( g : darr-from B E b (f 0₂))
  : is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) (f)
  → hom (E (b 1₂)) (f 1₂) (g 1₂)
  := \ is-locally-cocart →
    first (first (is-locally-cocart (g 1₂) (\ t → g t)))

#def fill-locally-cocartesian-arrow
  ( B : U)
  ( E : B → U)
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  ( g : darr-from B E b (f 0₂))
  ( f-loc-cocart : is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) (f))
  : dhom2-over-arrow B b
    E (f 0₂) (f 1₂) (g 1₂)
    f (hom-fill-locally-cocartesian-arrow B E b f g f-loc-cocart) (\ t → g t)
  :=
    second (first (f-loc-cocart (g 1₂) (\ t → g t)))

#def all-equal-fill-locally-cocartesian-arrow
  ( B : U)
  ( E : B → U)
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  ( g : darr-from B E b (f 0₂))
  ( f-loc-cocart : is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) (f))
  ( h h' : hom (E (b 1₂)) (f 1₂) (g 1₂))
  ( a : dhom2-over-arrow B b E (f 0₂) (f 1₂) (g 1₂) f h (\ t → g t))
  ( a' : dhom2-over-arrow B b E (f 0₂) (f 1₂) (g 1₂) f h' (\ t → g t))
  : h =_{hom (E (b 1₂)) (f 1₂) (g 1₂)} h'
  :=
    ap
      ( Σ ( h : hom (E (b 1₂)) (f 1₂) (g 1₂))
      , dhom2-over-arrow B b E (f 0₂) (f 1₂) (g 1₂) f h (\ t → g t))
      ( hom (E (b 1₂)) (f 1₂) (g 1₂))
      ( h , a)
      ( h' , a')
      ( \ x → first x)
      ( all-elements-equal-is-contr
        ( Σ ( h : hom (E (b 1₂)) (f 1₂) (g 1₂))
          , dhom2-over-arrow B b E (f 0₂) (f 1₂) (g 1₂) f h (\ t → g t))
        ( f-loc-cocart (g 1₂) (\ t → g t))
        ( h , a)
        ( h' , a'))

#def is-id-locally-cocartesian-arrow
  ( B : U)
  ( E : B → U)
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  ( f-loc-cocart : is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) (f))
  ( h : hom (E (b 1₂)) (f 1₂) (f 1₂))
  ( a : dhom2-over-arrow B b E (f 0₂) (f 1₂) (f 1₂) f h f)
  : h =_{hom (E (b 1₂)) (f 1₂) (f 1₂)} (id-hom (E (b 1₂)) (f 1₂))
  :=
    all-equal-fill-locally-cocartesian-arrow B E b f f f-loc-cocart
      h (id-hom (E (b 1₂)) (f 1₂)) a (\ (x , y) → f x)
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

#def inv-lift-id-locally-cocartesian
  ( b : B) (e : E b)
  : hom (E b) (action-locally-cocartesian (id-hom B b) e) (e)
  := hom-fill-locally-cocartesian-arrow B E (id-hom B b)
    ( first (second (lifts b b (id-hom B b) e)))
    ( \ t → e)
    ( second (second (lifts b b (id-hom B b) e)))

#def lift-id-locally-cocartesian
  ( b : B) (e : E b)
  : hom (E b) (e) (action-locally-cocartesian (id-hom B b) e)
  := first (second (lifts (b) (b) (id-hom B b) e))

#def is-locally-cocartesian-arrow-lift-id-locally-cocartesian
  ( b : B) (e : E b)
  : is-locally-cocartesian-arrow B (b) (b) (id-hom B b)
    E (e) (action-locally-cocartesian (id-hom B b) e) (lift-id-locally-cocartesian b e)
  := second (second (lifts b b (id-hom B b) e))

-- #def hom2-id-action-id-locally-cocartesian
--   ( b : B)
--   ( e : E b)
--   : hom2 (E b)
--     ( e) (action-locally-cocartesian (id-hom B b) e) (e)
--     ( lift-id-locally-cocartesian' b e)
--     ( lift-id-locally-cocartesian b e)
--     ( id-hom (E b) e)
--   :=
--     fill-locally-cocartesian-arrow B E (id-hom B b)
--       ( first (second (lifts b b (id-hom B b) e)))
--       ( \ t → e)
--       ( second (second (lifts b b (id-hom B b) e)))

#variable segal-fibers : (b : B) → is-segal (E b)


#def is-section-lift-id-locally-cocartesian uses (lifts)
  ( b : B)
  ( e : E b)
  : comp-is-segal
    ( E b) (segal-fibers b)
    ( e) (action-locally-cocartesian (id-hom B b) e) (e)
    ( lift-id-locally-cocartesian b e)
    ( inv-lift-id-locally-cocartesian b e)
    = ( id-hom (E b) e)
  :=
    uniqueness-comp-is-segal
      ( E b) (segal-fibers b)
      ( e) (action-locally-cocartesian (id-hom B b) e) (e)
      ( lift-id-locally-cocartesian b e)
      ( inv-lift-id-locally-cocartesian b e)
      ( id-hom (E b) e)
      ( fill-locally-cocartesian-arrow B E (id-hom B b)
        ( first (second (lifts b b (id-hom B b) e)))
        ( \ t → e)
        ( second (second (lifts b b (id-hom B b) e))))


#def lift-id-inv-lift-id-lift-id-is-lift-id-locally-cocartesian uses (lifts)
  ( b : B)
  ( e : E b)
  : comp-is-segal (E b) (segal-fibers b)
    ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
    ( lift-id-locally-cocartesian b e)
    ( comp-is-segal (E b) (segal-fibers b)
      ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( inv-lift-id-locally-cocartesian b e)
      ( lift-id-locally-cocartesian b e))
    = ( lift-id-locally-cocartesian b e)
  := triple-concat (hom (E b) e (action-locally-cocartesian (id-hom B b) e))
    ( comp-is-segal (E b) (segal-fibers b)
      ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
      ( lift-id-locally-cocartesian b e)
      ( comp-is-segal (E b) (segal-fibers b)
        ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
        ( inv-lift-id-locally-cocartesian b e)
        ( lift-id-locally-cocartesian b e)))
    ( comp-is-segal (E b) (segal-fibers b)
      ( e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( comp-is-segal (E b) (segal-fibers b)
        ( e) (action-locally-cocartesian (id-hom B b) e) (e)
        ( lift-id-locally-cocartesian b e)
        ( inv-lift-id-locally-cocartesian b e))
      ( lift-id-locally-cocartesian b e))
    ( comp-is-segal (E b) (segal-fibers b)
      ( e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( id-hom (E b) e)
      ( lift-id-locally-cocartesian b e))
    ( lift-id-locally-cocartesian b e) --
    ( rev-associative-is-segal extext (E b) (segal-fibers b)
      ( e) (action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( lift-id-locally-cocartesian b e)
      ( inv-lift-id-locally-cocartesian b e)
      ( lift-id-locally-cocartesian b e))
    (
      ap
        ( hom (E b) e e)
        ( hom (E b) e (action-locally-cocartesian (id-hom B b) e))
        ( comp-is-segal (E b) (segal-fibers b)
          ( e) (action-locally-cocartesian (id-hom B b) e) (e)
          ( lift-id-locally-cocartesian b e)
          ( inv-lift-id-locally-cocartesian b e))
        ( id-hom (E b) e)
        ( \ h → comp-is-segal (E b) (segal-fibers b)
          ( e) (e) (action-locally-cocartesian (id-hom B b) e)
          ( h)
          ( lift-id-locally-cocartesian b e))
        ( is-section-lift-id-locally-cocartesian b e))
    ( id-comp-is-segal (E b) (segal-fibers b)
      ( e) (action-locally-cocartesian (id-hom B b) e)
      ( lift-id-locally-cocartesian b e))


#def is-retraction-lift-id-locally-cocartesian uses (extext lifts)
  ( b : B)
  ( e : E b)
  : comp-is-segal (E b) (segal-fibers b)
    ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
    ( inv-lift-id-locally-cocartesian b e)
    ( lift-id-locally-cocartesian b e)
  = id-hom (E b) (action-locally-cocartesian (id-hom B b) e)
  :=
    is-id-locally-cocartesian-arrow B E
      ( id-hom B b)
      ( lift-id-locally-cocartesian b e)
      ( is-locally-cocartesian-arrow-lift-id-locally-cocartesian b e)
      ( comp-is-segal (E b) (segal-fibers b)
        ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
        ( inv-lift-id-locally-cocartesian b e)
        ( lift-id-locally-cocartesian b e))
      ( transport
        ( hom (E b) e (action-locally-cocartesian (id-hom B b) e))
        ( \ h → hom2 (E b)
          ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
          ( lift-id-locally-cocartesian b e)
          ( comp-is-segal (E b) (segal-fibers b)
            ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
            ( inv-lift-id-locally-cocartesian b e)
            ( lift-id-locally-cocartesian b e))
          ( h))
        ( comp-is-segal (E b) (segal-fibers b)
          ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
          ( lift-id-locally-cocartesian b e)
          ( comp-is-segal (E b) (segal-fibers b)
            ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
            ( inv-lift-id-locally-cocartesian b e)
            ( lift-id-locally-cocartesian b e)))
        ( lift-id-locally-cocartesian b e)
        ( lift-id-inv-lift-id-lift-id-is-lift-id-locally-cocartesian b e)
        ( witness-comp-is-segal (E b) (segal-fibers b)
          ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
          ( lift-id-locally-cocartesian b e)
          ( comp-is-segal (E b) (segal-fibers b)
            ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
            ( inv-lift-id-locally-cocartesian b e)
            ( lift-id-locally-cocartesian b e))))

#def is-iso-arrow-lift-id-locally-cocartesian uses (extext lifts)
  ( b : B)
  ( e : E b)
  : is-iso-arrow (E b) (segal-fibers b)
    ( e) (action-locally-cocartesian (id-hom B b) e)
    ( lift-id-locally-cocartesian b e)
  := is-iso-arrow-has-inverse-arrow (E b) (segal-fibers b)
    ( e) (action-locally-cocartesian (id-hom B b) e)
    ( lift-id-locally-cocartesian b e)
    ( inv-lift-id-locally-cocartesian b e
    , ( is-section-lift-id-locally-cocartesian b e
      , is-retraction-lift-id-locally-cocartesian b e))

```
