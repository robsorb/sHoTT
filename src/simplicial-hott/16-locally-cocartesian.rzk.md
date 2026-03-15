# "Locally" cocartesian families



This is a literate `rzk` file:

```rzk
#lang rzk-1
```


```rzk
#assume funext : FunExt
#assume extext : ExtExt
```


```rzk


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
  := dhom2 B (b 0₂) (b 1₂) (b 1₂) b (id-hom B (b 1₂)) b (degen-Δ²-cod B b)
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
      ( comp-over-Inner B E E-inner (degen-Δ²-cod B b) f)
  → is-locally-cocartesian-arrow B (b 0₂) (b 1₂) b E (f 0₂) (f 1₂) f
  := \ is-equiv-comp e'' h →
    is-contr-equiv-is-contr
      ( fib
        ( arr-from (E (b 1₂)) (f 1₂))
        ( darr-from B E b (f 0₂))
        ( comp-over-Inner B E E-inner (degen-Δ²-cod B b) f)
        ( h))
      ( ( Σ ( g : hom (E (b 1₂)) (f 1₂) e'')
        , ( dhom2 B (b 0₂) (b 1₂) (b 1₂) b (id-hom B (b 1₂)) b (degen-Δ²-cod B b)
          E (f 0₂) (f 1₂) e'' f g h)))
      ( equiv-fib-comp-dtriangles-Inner B E E-inner (degen-Δ²-cod B b) f h)
      ( is-contr-map-is-equiv
        ( arr-from (E (b 1₂)) (f 1₂))
        ( darr-from B E b (f 0₂))
        ( comp-over-Inner B E E-inner (degen-Δ²-cod B b) f)
        ( is-equiv-comp)
        ( h))


#end is-equiv-composition

```

## Locally cocartesian families are cocartesian

```rzk

#variable B : U
#variable E : B → U
#variable lifts : has-locally-cocartesian-lifts B E
#variable E-inner : is-inner B E


#def action-locally-cocartesian
  : ( f : Δ¹ → B) → E (f 0₂) → E (f 1₂)
  := \ f e → first (lifts (f 0₂) (f 1₂) f e)

#def lift-locally-cocartesian
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : dhom B (f 0₂) (f 1₂) f E e (action-locally-cocartesian f e)
  := first (second (lifts (f 0₂) (f 1₂) (f) e))

#def is-locally-cocartesian-lift-locally-cocartesian
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : is-locally-cocartesian-arrow B (f 0₂) (f 1₂) (f)
    E (e) (action-locally-cocartesian f e)  (lift-locally-cocartesian f e)
  := second (second (lifts (f 0₂) (f 1₂) (f) e))

#def lift-id-locally-cocartesian uses (lifts)
  ( b : B) (e : E b)
  : hom (E b) (e) (action-locally-cocartesian (id-hom B b) e)
  := lift-locally-cocartesian (id-hom B b) e

#def is-locally-cocartesian-arrow-lift-id-locally-cocartesian uses (lifts)
  ( b : B) (e : E b)
  : is-locally-cocartesian-arrow B (b) (b) (id-hom B b)
    E (e) (action-locally-cocartesian (id-hom B b) e) (lift-id-locally-cocartesian b e)
  := is-locally-cocartesian-lift-locally-cocartesian (id-hom B b) e

#def inv-lift-id-locally-cocartesian uses (lifts)
  ( b : B) (e : E b)
  : hom (E b) (action-locally-cocartesian (id-hom B b) e) (e)
  := hom-fill-locally-cocartesian-arrow B E (id-hom B b)
    ( lift-id-locally-cocartesian b e)
    ( \ t → e)
    ( is-locally-cocartesian-arrow-lift-id-locally-cocartesian b e)


#variable rezk-fibers : (b : B) → is-rezk (E b)

#def is-section-lift-id-locally-cocartesian uses (lifts)
  ( b : B)
  ( e : E b)
  : comp-is-segal
    ( E b) (is-segal-is-rezk (E b) (rezk-fibers b))
    ( e) (action-locally-cocartesian (id-hom B b) e) (e)
    ( lift-id-locally-cocartesian b e)
    ( inv-lift-id-locally-cocartesian b e)
    = ( id-hom (E b) e)
  :=
    uniqueness-comp-is-segal
      ( E b) (is-segal-is-rezk (E b) (rezk-fibers b))
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
  : comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
    ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
    ( lift-id-locally-cocartesian b e)
    ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
      ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( inv-lift-id-locally-cocartesian b e)
      ( lift-id-locally-cocartesian b e))
    = ( lift-id-locally-cocartesian b e)
  := triple-concat (hom (E b) e (action-locally-cocartesian (id-hom B b) e))
    ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
      ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
      ( lift-id-locally-cocartesian b e)
      ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
        ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
        ( inv-lift-id-locally-cocartesian b e)
        ( lift-id-locally-cocartesian b e)))
    ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
      ( e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
        ( e) (action-locally-cocartesian (id-hom B b) e) (e)
        ( lift-id-locally-cocartesian b e)
        ( inv-lift-id-locally-cocartesian b e))
      ( lift-id-locally-cocartesian b e))
    ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
      ( e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( id-hom (E b) e)
      ( lift-id-locally-cocartesian b e))
    ( lift-id-locally-cocartesian b e) --
    ( rev-associative-is-segal extext (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
      ( e) (action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
      ( lift-id-locally-cocartesian b e)
      ( inv-lift-id-locally-cocartesian b e)
      ( lift-id-locally-cocartesian b e))
    (
      ap
        ( hom (E b) e e)
        ( hom (E b) e (action-locally-cocartesian (id-hom B b) e))
        ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
          ( e) (action-locally-cocartesian (id-hom B b) e) (e)
          ( lift-id-locally-cocartesian b e)
          ( inv-lift-id-locally-cocartesian b e))
        ( id-hom (E b) e)
        ( \ h → comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
          ( e) (e) (action-locally-cocartesian (id-hom B b) e)
          ( h)
          ( lift-id-locally-cocartesian b e))
        ( is-section-lift-id-locally-cocartesian b e))
    ( id-comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
      ( e) (action-locally-cocartesian (id-hom B b) e)
      ( lift-id-locally-cocartesian b e))


#def is-retraction-lift-id-locally-cocartesian uses (extext lifts)
  ( b : B)
  ( e : E b)
  : comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
    ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
    ( inv-lift-id-locally-cocartesian b e)
    ( lift-id-locally-cocartesian b e)
  = id-hom (E b) (action-locally-cocartesian (id-hom B b) e)
  :=
    is-id-locally-cocartesian-arrow B E
      ( id-hom B b)
      ( lift-id-locally-cocartesian b e)
      ( is-locally-cocartesian-arrow-lift-id-locally-cocartesian b e)
      ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
        ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
        ( inv-lift-id-locally-cocartesian b e)
        ( lift-id-locally-cocartesian b e))
      ( transport
        ( hom (E b) e (action-locally-cocartesian (id-hom B b) e))
        ( \ h → hom2 (E b)
          ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
          ( lift-id-locally-cocartesian b e)
          ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
            ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
            ( inv-lift-id-locally-cocartesian b e)
            ( lift-id-locally-cocartesian b e))
          ( h))
        ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
          ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
          ( lift-id-locally-cocartesian b e)
          ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
            ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
            ( inv-lift-id-locally-cocartesian b e)
            ( lift-id-locally-cocartesian b e)))
        ( lift-id-locally-cocartesian b e)
        ( lift-id-inv-lift-id-lift-id-is-lift-id-locally-cocartesian b e)
        ( witness-comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
          ( e) (action-locally-cocartesian (id-hom B b) e) (action-locally-cocartesian (id-hom B b) e)
          ( lift-id-locally-cocartesian b e)
          ( comp-is-segal (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
            ( action-locally-cocartesian (id-hom B b) e) (e) (action-locally-cocartesian (id-hom B b) e)
            ( inv-lift-id-locally-cocartesian b e)
            ( lift-id-locally-cocartesian b e))))

#def is-iso-arrow-inv-lift-id-locally-cocartesian uses (extext lifts)
  ( b : B)
  ( e : E b)
  : is-iso-arrow (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
    ( action-locally-cocartesian (id-hom B b) e) (e)
    ( inv-lift-id-locally-cocartesian b e)
  := is-iso-arrow-has-inverse-arrow (E b) (is-segal-is-rezk (E b) (rezk-fibers b))
    ( action-locally-cocartesian (id-hom B b) e) (e)
    ( inv-lift-id-locally-cocartesian b e)
    ( lift-id-locally-cocartesian b e
    , ( is-retraction-lift-id-locally-cocartesian b e
      , is-section-lift-id-locally-cocartesian b e))

#def action-unit-locally-cocartesian uses (extext lifts)
  ( b : B)
  ( e : E b)
  : action-locally-cocartesian (id-hom B b) e = e
  := eq-iso-is-rezk (E b) (rezk-fibers b)
    ( action-locally-cocartesian (id-hom B b) e)
    ( e)
    ( inv-lift-id-locally-cocartesian b e
    , is-iso-arrow-inv-lift-id-locally-cocartesian b e)

#def hom-fill-is-id-locally-cocartesian uses (lifts)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : hom-fill-locally-cocartesian-arrow B E f
    ( lift-locally-cocartesian f e)
    ( lift-locally-cocartesian f e)
    ( is-locally-cocartesian-lift-locally-cocartesian f e)
    = id-hom (E (f 1₂)) (action-locally-cocartesian f e)
  := all-equal-fill-locally-cocartesian-arrow B E
    f
    ( lift-locally-cocartesian f e)
    ( lift-locally-cocartesian f e)
    ( is-locally-cocartesian-lift-locally-cocartesian f e)
    ( hom-fill-locally-cocartesian-arrow B E f
      ( lift-locally-cocartesian f e)
      ( lift-locally-cocartesian f e)
      ( is-locally-cocartesian-lift-locally-cocartesian f e))
    ( id-hom (E (f 1₂)) (action-locally-cocartesian f e))
    ( fill-locally-cocartesian-arrow B E f
      ( lift-locally-cocartesian f e)
      ( lift-locally-cocartesian f e)
      ( is-locally-cocartesian-lift-locally-cocartesian f e))
    ( \ (x , y) → lift-locally-cocartesian f e x)

#def square-lift-lift'-locally-cocartesian uses (lifts)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : ( ( x , y) : 2 × 2) → E (f x)
    [x ≡ 0₂ ↦ inv-lift-id-locally-cocartesian (f 0₂) e y
    , x ≡ 1₂ ↦ (action-locally-cocartesian f e)
    , y ≡ 0₂ ↦ lift-action B E action-locally-cocartesian f e x
    , y ≡ 1₂ ↦ lift-locally-cocartesian f e x]
  :=
    transport
      ( hom (E (f 1₂)) (action-locally-cocartesian f e) (action-locally-cocartesian f e))
      ( \ h → ((x , y) : 2 × 2) → E (f x)
        [x ≡ 0₂ ↦ inv-lift-id-locally-cocartesian (f 0₂) e y
        , x ≡ 1₂ ↦ h y
        , y ≡ 0₂ ↦ lift-action B E action-locally-cocartesian f e x
        , y ≡ 1₂ ↦ lift-locally-cocartesian f e x])
      ( hom-fill-locally-cocartesian-arrow B E f
        ( lift-locally-cocartesian f e)
        ( lift-locally-cocartesian f e)
        ( is-locally-cocartesian-lift-locally-cocartesian f e))
      ( id-hom (E (f 1₂)) (action-locally-cocartesian f e))
      ( hom-fill-is-id-locally-cocartesian f e)
      ( \ (x , y) →
        hom-fill-locally-cocartesian-arrow B E (clamp B f (x , 0₂))
          ( lift-locally-cocartesian (clamp B f (x , 0₂)) e)
          ( dclamp B E f (lift-locally-cocartesian f e) (x , 0₂))
          ( is-locally-cocartesian-lift-locally-cocartesian (clamp B f (x , 0₂)) e)
          y)

#def eq-lift'-lift-locally-cocartesian uses (extext lifts)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : lift-action B E action-locally-cocartesian f e
    =_{(t : Δ¹) → E (f t)} lift-locally-cocartesian f e
  := eq-weakly-degen-square-Inner B E E-inner
    f
    ( action-locally-cocartesian (id-hom B (f 0₂)) e)
    ( e)
    ( action-locally-cocartesian f e)
    ( action-locally-cocartesian f e)
    ( action-unit-locally-cocartesian (f 0₂) e)
    refl
    ( transport-rev
      ( hom (E (f 0₂)) (action-locally-cocartesian (id-hom B (f 0₂)) e) e)
      ( \ h → ((x , y) : 2 × 2) → E (f x)
        [x ≡ 0₂ ↦ h y
        , x ≡ 1₂ ↦ (action-locally-cocartesian f e)
        , y ≡ 0₂ ↦ lift-action B E action-locally-cocartesian f e x
        , y ≡ 1₂ ↦ lift-locally-cocartesian f e x])
      ( hom-eq (E (f 0₂)) (action-locally-cocartesian (id-hom B (f 0₂)) e) (e)
        ( action-unit-locally-cocartesian (f 0₂) e))
      ( inv-lift-id-locally-cocartesian (f 0₂) e)
      ( compute-first-iso-eq-eq-iso-is-rezk (E (f 0₂)) (rezk-fibers (f 0₂))
        ( action-locally-cocartesian (id-hom B (f 0₂)) e)
        ( e)
        ( inv-lift-id-locally-cocartesian (f 0₂) e
        , is-iso-arrow-inv-lift-id-locally-cocartesian (f 0₂) e))
      ( square-lift-lift'-locally-cocartesian f e))

#def is-locally-cocartesian-lift'-locally-cocartesian uses (extext lifts E-inner rezk-fibers)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : is-locally-cocartesian-arrow B (f 0₂) (f 1₂) (f)
    E
    ( action-locally-cocartesian (id-hom B (f 0₂)) e)
    ( action-locally-cocartesian f e)
    ( \ t → lift-action B E action-locally-cocartesian f e t)
  := transport-rev
    ( ( t : Δ¹) → E (f t))
    ( \ h → is-locally-cocartesian-arrow B (f 0₂) (f 1₂) (f)
      E
      ( h 0₂)
      ( h 1₂)
      ( \ t → h t))
    ( lift-action B E action-locally-cocartesian f e)
    ( lift-locally-cocartesian f e)
    ( eq-lift'-lift-locally-cocartesian f e)
    ( is-locally-cocartesian-lift-locally-cocartesian f e)


#def comp-action-locally-cocartesian uses (lifts)
  ( f : Δ¹ → B)
  ( g : (t : Δ¹) → B [t ≡ 0₂ ↦ f 1₂])
  : ( E (f 0₂)) → (E (g 1₂))
  := \ e → action-locally-cocartesian g (action-locally-cocartesian f e)




#def htpy-zigzag-unit-locally-cocartesian uses (extext lifts rezk-fibers)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  ( x : Δ¹)
  : comp-action-locally-cocartesian (id-hom B (f 0₂)) (clamp B f (x , 0₂)) e
  = comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e
  := zig-zag-concat (E (f x))
    ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (clamp B f (x , 0₂)) e)
    ( action-locally-cocartesian (clamp B f (x , 0₂)) e)
    ( comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e)
    ( ap (E (f 0₂)) (E (f x))
      ( action-locally-cocartesian (id-hom B (f 0₂)) e)
      ( e)
      ( action-locally-cocartesian (clamp B f (x , 0₂)))
      ( action-unit-locally-cocartesian (f 0₂) e))
    ( action-unit-locally-cocartesian (f x)
      ( action-locally-cocartesian (clamp B f (x , 0₂)) e))

#def dom-htpy-zigzag-unit-is-refl-locally-cocartesian uses (extext lifts rezk-fibers)
  ( b : B)
  ( e : E b)
  : htpy-zigzag-unit-locally-cocartesian (id-hom B b) e 0₂ = refl
  := ind-htpy-end funext
    ( E b)
    ( \ x → E b)
    ( identity (E b))
    ( \ f H → (e : E b)
    → ( zig-zag-concat (E b) (f (f e)) (f e) (f (f e))
        ( ap (E b) (E b) (f e) (e) f (H e))
        ( H (f e))) = refl)
    ( \ e → refl)
    ( action-locally-cocartesian (id-hom B b))
    ( action-unit-locally-cocartesian b)
    ( e)

#def square-zigzag-unit-locally-cocartesian uses (extext lifts rezk-fibers)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : ( ( x , y) : 2 × 2) → E (f x)
  := \ (x , y) →
    hom-eq (E (f x))
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (clamp B f (x , 0₂)) e)
      ( comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e)
      ( htpy-zigzag-unit-locally-cocartesian f e x)
      y

#def square-zigzag-unit-locally-cocartesian' uses (funext extext lifts rezk-fibers)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : ( ( x , y) : 2 × 2) → E (f x)
    [y ≡ 0₂ ↦
      comp-action-locally-cocartesian (id-hom B (f 0₂)) (clamp B f (x , 0₂)) e
    , y ≡ 1₂ ↦
      comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e
    , x ≡ 0₂ ↦
      comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e
    , x ≡ 1₂ ↦
      square-zigzag-unit-locally-cocartesian f e (1₂ , y)]
  := transport
    ( hom (E (f 0₂))
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e))
    ( \ h → ((x , y) : 2 × 2) → E (f x)
      [y ≡ 0₂ ↦
        -- comp-action-locally-cocartesian (id-hom B (f 0₂)) (clamp B f (x , 0₂)) e
        lift-action B E (action-locally-cocartesian) f
          ( action-locally-cocartesian (id-hom B (f 0₂)) e) x
      , y ≡ 1₂ ↦
        comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e
      , x ≡ 0₂ ↦ h y
      , x ≡ 1₂ ↦
        square-zigzag-unit-locally-cocartesian f e (1₂ , y)])
    ( \ y → square-zigzag-unit-locally-cocartesian f e (0₂ , y))
    ( id-hom (E (f 0₂))
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e))
    ( ap
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e
        = comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
      ( hom (E (f 0₂))
        ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
        ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e))
      ( htpy-zigzag-unit-locally-cocartesian f e 0₂)
      ( refl)
      ( \ p → hom-eq (E (f 0₂))
        ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
        ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
        p)
      ( dom-htpy-zigzag-unit-is-refl-locally-cocartesian (f 0₂) e))
    ( square-zigzag-unit-locally-cocartesian f e)

#def dhom2-zigzag-locally-cocartesian uses (funext extext lifts rezk-fibers)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : dhom2-over-arrow B f E
    ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
    ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (f) e)
    ( comp-action-locally-cocartesian (f) (id-hom B (f 1₂)) e)
    ( \ t → lift-action B E (action-locally-cocartesian) f
      ( action-locally-cocartesian (id-hom B (f 0₂)) e) t)
    ( \ y → square-zigzag-unit-locally-cocartesian f e (1₂ , y))
    ( \ x → comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e)
  := transport
    ( dhom B (f 0₂) (f 1₂) (f) E
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
      ( comp-action-locally-cocartesian (f) (id-hom B (f 1₂)) e))
    ( \ h → dhom2-over-arrow B f E
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (f) e)
      ( comp-action-locally-cocartesian (f) (id-hom B (f 1₂)) e)
      ( \ t → lift-action B E (action-locally-cocartesian) f
        ( action-locally-cocartesian (id-hom B (f 0₂)) e) t)
      ( \ y → square-zigzag-unit-locally-cocartesian f e (1₂ , y))
      h)
    ( \ t → square-zigzag-unit-locally-cocartesian' f e (t , t))
    ( \ x → comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e)
    ( eq-darr-from-degen-dtriangle'-Inner B E E-inner
      f
      ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
      ( \ x → square-zigzag-unit-locally-cocartesian f e (x , 1₂))
      ( \ (y , x) → square-zigzag-unit-locally-cocartesian' f e (x , y)))
    ( \ (x , y) → square-zigzag-unit-locally-cocartesian' f e (x , y))

#def dhom2-coherence-locally-cocartesian uses (lifts)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : dhom2-over-arrow B f E
    ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (id-hom B (f 0₂)) e)
    ( comp-action-locally-cocartesian (id-hom B (f 0₂)) (f) e)
    ( comp-action-locally-cocartesian (f) (id-hom B (f 1₂)) e)
    ( \ t → lift-action B E (action-locally-cocartesian) f
      ( action-locally-cocartesian (id-hom B (f 0₂)) e) t)
    ( coherence-hom-action B E (action-locally-cocartesian) f e)
    ( \ x → comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e)
  := \ (x , y) →
    action-locally-cocartesian (clamp B f (x , y))
      ( action-locally-cocartesian (clamp B f (y , 0₂)) e)

#def is-coherent-action-locally-cocartesian uses (funext extext lifts E-inner rezk-fibers)
  : is-coherent-action B E (action-locally-cocartesian) (action-unit-locally-cocartesian)
  := \ f e → all-equal-fill-locally-cocartesian-arrow B E f
    ( lift-action B E (action-locally-cocartesian) f
      ( action-locally-cocartesian (id-hom B (f 0₂)) e))
    ( \ x → comp-action-locally-cocartesian (clamp B f (x , 0₂)) (id-hom B (f x)) e)
    ( is-locally-cocartesian-lift'-locally-cocartesian f
      ( action-locally-cocartesian (id-hom B (f 0₂)) e))
    ( coherence-hom-action B E (action-locally-cocartesian) f e)
    ( \ y → square-zigzag-unit-locally-cocartesian f e (1₂ , y))
    ( dhom2-coherence-locally-cocartesian f e)
    ( dhom2-zigzag-locally-cocartesian f e)


#def is-cocartesian-locally-cocartesian uses (funext extext lifts E-inner rezk-fibers)
  : has-cocartesian-lifts B E
  := has-cocart-lifts-coherent-action
    funext
    extext
    B E
    action-locally-cocartesian
    E-inner
    action-unit-locally-cocartesian
    is-coherent-action-locally-cocartesian
```
