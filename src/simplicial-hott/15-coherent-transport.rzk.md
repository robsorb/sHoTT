# Coherent transport


```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
#assume extext : ExtExt

```

## Clamping morphisms

```rzk
#section clamping

#variables B : U


#def clamp (f : Δ¹ → B) ((u , l) : Δ²)
  : hom B (f l) (f u)
  := \ t → recOR (t ≤ l ↦ f l
  , l ≤ t ↦ recOR (u ≤ t ↦ f u , t ≤ u ↦ f t))


#def clamp-commutes
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : ( ( x , y) : Δ²) → B
    [y ≡ 0₂ ↦ clamp f (t , 0₂) x
    , x ≡ 1₂ ↦ clamp f (1₂ , t) y
    , x ≡ y ↦ f x]
  := \ (x , y) → clamp f (x , y) t

#variable E : B → U

#def dclamp
  ( f : Δ¹ → B)
  ( g : (t : Δ¹) → E (f t))
  ( ( u , l) : Δ²)
  : dhom B (f l) (f u) (clamp f (u , l)) E (g l) (g u)
  := \ t → recOR (t ≤ l ↦ g l , l ≤ t ↦
    recOR (u ≤ t ↦ g u , t ≤ u ↦ g t))

```

## The horizontal edges along a simplex

```rzk

#def hor-edge-Δ²
  ( a : Δ² → B)
  ( y : Δ¹)
  : hom B (a (y , y)) (a (1₂ , y))
  := \ x → recOR (x ≤ y ↦ a (y , y) , y ≤ x ↦ a (x , y))

#end clamping
```

## Lifts from transport

```rzk

#variable B : U
#variable E : B → U
#variable action : (f : Δ¹ → B) → E (f 0₂) → E (f 1₂)
```

### Lifts of edges

```rzk
#def lift-action (f : Δ¹ → B) (e : E (f 0₂))
  : darr-from B E f (action (id-hom B (f 0₂)) e)
  := \ t → action (clamp B f (t , 0₂)) e

```

### Lifts of triangles

```rzk

#def lift-2-action uses (action)
  ( a : Δ² → B)
  ( h : (t : Δ¹) → E (comp-Δ² B a t))
  : ( t : Δ²) → E (a t)
  := \ (x , y) → lift-action (hor-edge-Δ² B a y) (h y) x

#def lift-2-action-fst uses (action)
  ( a : Δ² → B)
  ( h : (t : Δ¹) → E (comp-Δ² B a t))
  : fst-dΔ² B E a (lift-2-action a h) = lift-action (fst-Δ² B a) (h 0₂)
  := refl

#def lift-2-action-comp uses (action)
  ( a : Δ² → B)
  ( h : (t : Δ¹) → E (comp-Δ² B a t))
  : comp-dΔ² B E a (lift-2-action a h) = (\ t → action (id-hom B (a (t , t))) (h t))
  := refl

```

These morphisms will be the inverse of composition with our lifts.

```rzk
#def inv-comp-lift-action uses (action)
  ( a : Δ² → B)
  :
  ( ( t : Δ¹) → E (comp-Δ² B a t)) → ((t : Δ¹) → E (snd-Δ² B a t))
  := \ h → snd-dΔ² B E a (lift-2-action a h)

#def inv-tot-comp-lift-action
  ( a : Δ² → B)
  : ( ( t : Δ¹) → E (comp-Δ² B a t))
  → ( Σ ( e' : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e'))
  := \ h → (h 0₂ , inv-comp-lift-action a h)

```

### Pushforward of dependent triangles

```rzk
#def action-dtriangle
  ( a : Δ² → B)
  ( da : (t : Δ²) → E (a t))
  : ( ( x , y) : Δ²) → E (snd-Δ² B a y)
  := \ (x , y) → action (clamp B (hor-edge-Δ² B a y) (1₂ , x)) (da (x , y))

#def action-dtriangle-comp uses (action)
  ( a : Δ² → B)
  ( da : (t : Δ²) → E(a t))
  ( t : Δ¹)
  : ( action-dtriangle a da) (t , t) = inv-comp-lift-action a (comp-dΔ² B E a da) t
  := refl

#def action-dtriangle-snd uses (action)
  ( a : Δ² → B)
  ( da : (t : Δ²) → E(a t))
  ( t : Δ¹)
  : ( action-dtriangle a da) (1₂ , t)
    = action (id-hom B (snd-Δ² B a t)) ((snd-dΔ² B E a da) t)
  := refl

#def action-dtriangle-fst uses (action)
  ( a : Δ² → B)
  ( da : (t : Δ²) → E(a t))
  ( t : Δ¹)
  : ( action-dtriangle a da) (t , 0₂)
    = action (clamp B (fst-Δ² B a) (1₂ , t)) (fst-dΔ² B E a da t)
  := refl

```


## Composing with lifts

We want to show that the lifts induced by our action are cocartesian.
Hence we want to show that the following map is an equivalence.

```rzk
#variables E-inner : is-inner B E


#def comp-lift-action
  ( a : Δ² → B)
  ( e : E (a (0₂ , 0₂)))
  : ( darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
  → ( darr-from B E (comp-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))
  := \ g →
    comp-over-Inner B E E-inner
      a
      ( lift-action (fst-Δ² B a) e)
      g

#def fill-lift-action
  ( a : Δ² → B)
  ( e : E (a (0₂ , 0₂)))
  ( g : darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
  : ( t : Δ²) → E (a t)
  := fill-over-Inner B E
    E-inner
    a
    ( lift-action (fst-Δ² B a) e)
    g

#def fst-fill-lift uses (E-inner)
  ( a : Δ² → B)
  ( e : E (a (0₂ , 0₂)))
  ( g : darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
  : fst-dΔ² B E a (fill-lift-action a e g) = (lift-action (fst-Δ² B a) e)
  := refl
```


We will do this by proving that the total map is an equivalence.
If our action preserves identities it suffices to show that the following map is an equivalence.

```rzk

#def tot-comp-lift-action uses (E-inner)
  ( a : Δ² → B)
  : ( Σ ( e' : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e'))
  → ( ( t : Δ¹) → E (comp-Δ² B a t))
  := \ (e , g) → comp-lift-action a e g

```

Our inverse is almost a right inverse to composition with our lift.

```rzk

#def apply-action-id-darr
  ( f : Δ¹ → B)
  ( h : (t : Δ¹) → E (f t))
  ( t : Δ¹)
  : E (f t)
  := action (id-hom B (f t)) (h t)

#def eq-comp-lift-inv-comp-lift-action-id uses (action)
  ( a : Δ² → B)
  ( h : (t : Δ¹) → E (comp-Δ² B a t))
  : comp-lift-action a (h 0₂) (inv-comp-lift-action a h)
    = apply-action-id-darr (comp-Δ² B a) h
  := eq-dtriangle-Inner B E E-inner a (lift-2-action a h)
```


## Preserving identities


```rzk
#variables action-id : (x : B) → (e : E x) → action (id-hom B x) e = e
```

We show that the codomain of the total map is simply a type of sections.
Therefore it suffices to show that `tot-comp-lift` is an equivalence.

```rzk
#def is-equiv-second-sigma-action-id-sections uses (action-id)
  ( f : Δ¹ → B)
  : is-equiv
    ( Σ ( e : E (f 0₂)) , darr-from B E f (action (id-hom B (f 0₂)) e))
    ( ( t : Δ¹) → E (f t))
    ( \ p → second p)
  := transport
    ( E (f 0₂) → E (f 0₂))
    ( \ act → is-equiv
      ( Σ ( e : E (f 0₂)) , darr-from B E f (act e))
      ( ( t : Δ¹) → E (f t))
      ( \ p → second p))
    ( identity (E (f 0₂)))
    ( action (id-hom B (f 0₂)))
    ( rev (E (f 0₂) → E (f 0₂)) (action (id-hom B (f 0₂))) (identity (E (f 0₂)))
      ( eq-htpy funext (E (f 0₂)) (\ x → E (f 0₂))
        ( action (id-hom B (f 0₂)))
        ( identity (E (f 0₂)))
        ( action-id (f 0₂))))
    ( is-equiv-has-inverse
      ( Σ ( e : E (f 0₂)) , darr-from B E f e)
      ( ( t : Δ¹) → E (f t))
      ( \ p → second p)
      ( \ g → (g 0₂ , g) , (\ x → refl , \ x → refl)))
```

### Right inverse to composition

We can now show that `inv-comp-lift` is a right inverse of `tot-comp-lift`.

```rzk

#def eq-action-id-darr-action-id uses (action action-id)
  ( a : Δ² → B) (h : (t : Δ¹) → E (comp-Δ² B a t))
  : apply-action-id-darr (comp-Δ² B a) h = h
  := naive-dedge-ext
      extext
      B
      E
      ( comp-Δ² B a)
      ( apply-action-id-darr (comp-Δ² B a) h)
      h
      ( \ t → action-id (a (t , t)) (h t))

#def eq-comp-lift-inv-comp-lift-id-action-id
  uses (extext action action-id E-inner)
  ( a : Δ² → B)
  ( h : (t : Δ¹) → E (comp-Δ² B a t))
  : comp-lift-action a (h 0₂) (inv-comp-lift-action a h)
    =_{(t : Δ¹) → E (comp-Δ² B a t)}
    h
  := concat
    ( ( t : Δ¹) → E (comp-Δ² B a t))
    ( comp-lift-action a (h 0₂) (inv-comp-lift-action a h))
    ( ( \ t → action (id-hom B (a (t , t))) (h t)))
    h
    ( eq-comp-lift-inv-comp-lift-action-id a h)
    ( eq-action-id-darr-action-id a h)


#def is-retraction-tot-comp-lift-action-id
  uses (extext E-inner action action-id)
  ( a : Δ² → B)
  ( h : (t : Δ¹) → E (comp-Δ² B a t))
  : tot-comp-lift-action a (inv-tot-comp-lift-action a h) = h
  := eq-comp-lift-inv-comp-lift-id-action-id a h

```


## Coherence

### The coherence condition

```rzk
#def coherence-hom-action
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : hom (E (f 1₂))
    ( action f (action (id-hom B (f 0₂)) e))
    ( action (id-hom B (f 1₂)) (action f e))
  := \ t → action (clamp B f (1₂ , t)) (lift-action f e t)

#def zig-zag-action
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : action f (action (id-hom B (f 0₂)) e) = action (id-hom B (f 1₂)) (action f e)
  := zig-zag-concat (E (f 1₂))
    ( action f (action (id-hom B (f 0₂)) e))
    ( action f e)
    ( action (id-hom B (f 1₂)) (action f e))
    ( ap
      ( E (f 0₂))
      ( E (f 1₂))
      ( action (id-hom B (f 0₂)) e)
      ( e)
      ( action f)
      ( action-id (f 0₂) e))
    ( action-id (f 1₂) (action f e))

#def hom-zigzag-action uses (action-id)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : hom (E (f 1₂))
    ( action f (action (id-hom B (f 0₂)) e))
    ( action (id-hom B (f 1₂)) (action f e))
  := hom-eq (E (f 1₂))
    ( action f (action (id-hom B (f 0₂)) e))
    ( action (id-hom B (f 1₂)) (action f e))
    ( zig-zag-action f e)

#def is-coherent-for-hom-action uses (action-id)
  ( f : Δ¹ → B)
  ( e : E (f 0₂))
  : U
  := coherence-hom-action f e = hom-zigzag-action f e

#def is-coherent-action uses (action action-id)
  : U
  := (f : Δ¹ → B) → (e : E (f 0₂)) → is-coherent-for-hom-action f e
```










## Preserving composition

We the other side we need to assume that our action preserves some compositions.

```rzk
#variables action-comp :
  ( f : Δ¹ → B)
  → ( e : E (f 0₂))
  → ( t : Δ¹)
  → action (clamp B f (1₂ , t)) (action (clamp B f (t , 0₂)) e) = action f e


#variable left-unit-coherence :
  ( f : Δ¹ → B)
  → ( e : E (f 0₂))
  → action-id (f 1₂) (action f e) = action-comp f e 1₂


#variable right-unit-coherence :
  ( f : Δ¹ → B)
  → ( e : E (f 0₂))
  → action-comp f e 0₂
    = ap
      ( E (f 0₂))
      ( E (f 1₂))
      ( action (id-hom B (f 0₂)) e)
      e
      ( action f)
      ( action-id (f 0₂) e)
```

### Left inverse to composition

```rzk
#section prf-cocart-coherent-action-left-inverse

#variables a : Δ² → B
#variables e : E (a (0₂ , 0₂))
#variables g : darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e)
```

We define some aliases for convenience.

```rzk

#def fid-cocart-prf
  : ( E (a (1₂ , 0₂)))
  := (action (fst-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))

#def f-cocart-prf
  : ( E (a (1₂ , 0₂)))
  := (action (fst-Δ² B a) e)

#def idf-cocart-prf
  : ( E (a (1₂ , 0₂)))
  := (action (id-hom B (a (1₂ , 0₂))) (action (fst-Δ² B a) e))
```


Applying the pushforward to `fill-lift` yeilds a weakly degenerate triangle.

```rzk

#def is-weakly-degen-action-fill-lift-coherent-action uses (E-inner)
  ( t : Δ¹)
  : ( fst-dΔ² B E (degen-Δ²-dom B (snd-Δ² B a)) (action-dtriangle a (fill-lift-action a e g))) t
    = action (fst-Δ² B a) e
  := action-comp (fst-Δ² B a) e t
```

This induces a homotopy between the diagonal (the inverse of composition) and the vertical one.

```rzk
#def htpy-inv-comp-lift-snd-action-fill-lift-coherent-action
  uses (extext action-comp)
  : htpy-from B E
    ( snd-Δ² B a)
    ( inv-comp-lift-action a (comp-lift-action a e g))
    ( snd-dΔ² B E (degen-Δ²-dom B (snd-Δ² B a)) (action-dtriangle a (fill-lift-action a e g)))
    ( concat
      ( E (a (1₂ , 0₂)))
      ( fid-cocart-prf)
      ( f-cocart-prf)
      ( idf-cocart-prf)
      ( action-comp (fst-Δ² B a) e 0₂)
      ( rev
        ( E (a (1₂ , 0₂)))
        ( idf-cocart-prf)
        ( f-cocart-prf)
        ( action-comp (fst-Δ² B a) e 1₂)))
  := htpy-from-weakly-degen-dtriangle extext B E
    E-inner
    ( snd-Δ² B a)
    ( action-dtriangle a (fill-lift-action a e g))
    ( action (fst-Δ² B a) e)
    ( is-weakly-degen-action-fill-lift-coherent-action)

#def htpy-snd-action-fill-lift-id-coherent-action uses (E-inner)
  : htpy-from B E
    ( snd-Δ² B a)
    ( snd-dΔ² B E (degen-Δ²-dom B (snd-Δ² B a)) (action-dtriangle a (fill-lift-action a e g)))
    ( g)
    ( action-id (a (1₂ , 0₂)) (g 0₂))
  := \ t → action-id (a (1₂ , t)) (g t)
```

The vertical edge is also homotopic to our original `g`.

```rzk
#def htpy-snd-action-fill-lift-id'-coherent-action uses (E-inner)
  : htpy-from B E
    ( snd-Δ² B a)
    ( snd-dΔ² B E (degen-Δ²-dom B (snd-Δ² B a)) (action-dtriangle a (fill-lift-action a e g)))
    ( g)
    ( action-comp (fst-Δ² B a) e 1₂)
  := transport
    ( idf-cocart-prf = f-cocart-prf)
    ( \ p → htpy-from B E
      ( snd-Δ² B a)
      ( snd-dΔ² B E (degen-Δ²-dom B (snd-Δ² B a)) (action-dtriangle a (fill-lift-action a e g)))
      ( g)
      ( p))
    ( action-id (a (1₂ , 0₂)) (g 0₂))
    ( action-comp (fst-Δ² B a) e 1₂)
    ( left-unit-coherence (fst-Δ² B a) e)
    ( htpy-snd-action-fill-lift-id-coherent-action)
```

We define a utility for concatenating homotopies and simultaneously cancelling inverse paths.

```rzk
#def concat-htpy-from-cancel-right
  ( b : Δ¹ → B)
  ( f : (t : Δ¹) → E (b t))
  ( g : (t : Δ¹) → E (b t))
  ( h : (t : Δ¹) → E (b t))
  ( p : f 0₂ = h 0₂)
  ( q : g 0₂ = h 0₂)
  ( H1 : htpy-from B E b f g (concat (E (b 0₂)) (f 0₂) (h 0₂) (g 0₂) p (rev (E (b 0₂)) (g 0₂) (h 0₂) q)))
  ( H2 : htpy-from B E b g h q)
  : htpy-from B E b f h p
  := transport
    ( f 0₂ = h 0₂)
    ( htpy-from B E b f h)
    ( concat
      ( E (b 0₂))
      ( f 0₂)
      ( g 0₂)
      ( h 0₂)
      ( concat (E (b 0₂)) (f 0₂) (h 0₂) (g 0₂) p (rev (E (b 0₂)) (g 0₂) (h 0₂) q))
      q)
    p
    ( section-postconcat (E (b 0₂)) (f 0₂) (g 0₂) (h 0₂) q p)
    ( concat-htpy-from B E
      b
      f g h
      ( concat (E (b 0₂)) (f 0₂) (h 0₂) (g 0₂) p (rev (E (b 0₂)) (g 0₂) (h 0₂) q))
      q
      H1
      H2)
```

We obtain a much simpler homotopy between the inverse of composition and our original `g`.

```rzk
#def htpy-inv-comp-lift-id-coherent-action
  uses (extext E-inner action-id left-unit-coherence)
  : htpy-from B E
    ( snd-Δ² B a)
    ( inv-comp-lift-action a (comp-lift-action a e g))
    ( g)
    ( action-comp (fst-Δ² B a) e 0₂)
  := concat-htpy-from-cancel-right
    ( snd-Δ² B a)
    ( inv-comp-lift-action a (comp-lift-action a e g))
    ( snd-dΔ² B E (degen-Δ²-dom B (snd-Δ² B a)) (action-dtriangle a (fill-lift-action a e g)))
    ( g)
    ( action-comp (fst-Δ² B a) e 0₂)
    ( action-comp (fst-Δ² B a) e 1₂)
    ( htpy-inv-comp-lift-snd-action-fill-lift-coherent-action)
    ( htpy-snd-action-fill-lift-id'-coherent-action)
```

We need to adjust the starting path so that it is in the right form for us to apply `eq-pullback-darr-from`.

```rzk
#def htpy-inv-comp-lift-id'-coherent-action
  uses (extext E-inner left-unit-coherence)
  : htpy-from B E
    ( snd-Δ² B a)
    ( inv-comp-lift-action a (comp-lift-action a e g))
    ( g)
    ( ap
      ( E (a (0₂ , 0₂)))
      ( E (a (1₂ , 0₂)))
      ( action (id-hom B (a (0₂ , 0₂))) e)
      e
      ( action (fst-Δ² B a))
      ( action-id (a (0₂ , 0₂)) e))
  := transport
    ( inv-comp-lift-action a (comp-lift-action a e g) 0₂ = g 0₂)
    ( \ p → htpy-from B E
      ( snd-Δ² B a)
      ( inv-comp-lift-action a (comp-lift-action a e g))
      ( g)
      p)
    ( action-comp (fst-Δ² B a) e 0₂)
    ( ap
      ( E (a (0₂ , 0₂)))
      ( E (a (1₂ , 0₂)))
      ( action (id-hom B (a (0₂ , 0₂))) e)
      e
      ( action (fst-Δ² B a))
      ( action-id (a (0₂ , 0₂)) e))
    ( right-unit-coherence (fst-Δ² B a) e)
    ( htpy-inv-comp-lift-id-coherent-action)
```

We conclude using `eq-pullback-darr-from`.


```rzk
#def is-section-comp-lift-coherent-action
  uses (extext E-inner action-comp left-unit-coherence right-unit-coherence)
  : ( action (id-hom B (a (0₂ , 0₂))) e , inv-comp-lift-action a (comp-lift-action a e g))
      =_{Σ (e' : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e')}
      ( e , g)
  := eq-pullback-darr-from extext B E
    ( a (0₂ , 0₂))
    ( snd-Δ² B a)
    ( action (fst-Δ² B a))
    ( action (id-hom B (a (0₂ , 0₂))) e)
    ( e)
    ( inv-comp-lift-action a (comp-lift-action a e g))
    ( action-id (a (0₂ , 0₂)) e)
    ( g)
    ( htpy-inv-comp-lift-id'-coherent-action)

#end prf-cocart-coherent-action-left-inverse
```

```rzk
#def is-section-tot-comp-lift-coherent-action
  uses (extext E-inner action-id action-comp left-unit-coherence right-unit-coherence)
  ( a : Δ² → B)
  ( ( e , g) : Σ (e : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
  : inv-tot-comp-lift-action a (tot-comp-lift-action a (e , g)) = (e , g)
  := is-section-comp-lift-coherent-action a e g
```

## Inner families with coherent action are (Segal)-cocartesian

```rzk
#def is-equiv-tot-comp-lift-coherent-action
  uses (extext E-inner action-id action-comp left-unit-coherence right-unit-coherence)
  ( a : Δ² → B)
  : is-equiv
    ( Σ ( e : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
    ( ( t : Δ¹) → E (comp-Δ² B a t))
    ( tot-comp-lift-action a)
  := is-equiv-has-inverse
    ( Σ ( e : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
    ( ( t : Δ¹) → E (comp-Δ² B a t))
    ( tot-comp-lift-action a)
    ( inv-tot-comp-lift-action a
    , ( is-section-tot-comp-lift-coherent-action a
      , is-retraction-tot-comp-lift-action-id a))


#def is-equiv-comp-lift-coherent-action
  uses (funext extext E-inner action-id action-comp left-unit-coherence right-unit-coherence)
  ( a : Δ² → B)
  : ( e : E (a (0₂ , 0₂))) → is-equiv
    ( darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
    ( darr-from B E (comp-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))
    ( comp-over-Inner B E E-inner a (lift-action (fst-Δ² B a) e))
  := is-equiv-fiberwise-is-equiv-total
    ( E (a (0₂ , 0₂)))
    ( \ e → darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
    ( \ e → darr-from B E (comp-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))
    ( \ e → comp-over-Inner B E E-inner a (lift-action (fst-Δ² B a) e))
    ( is-equiv-right-factor
      ( Σ ( e : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
      ( Σ ( e : E (a (0₂ , 0₂))) , darr-from B E (comp-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))
      ( ( t : Δ¹) → E (comp-Δ² B a t))
      ( total-map
        ( E (a (0₂ , 0₂)))
        ( \ e → darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
        ( \ e → darr-from B E (comp-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))
        ( comp-lift-action a))
      ( \ p → second p)
      ( is-equiv-second-sigma-action-id-sections (comp-Δ² B a))
      ( is-equiv-tot-comp-lift-coherent-action a))


#def has-cocart-lifts-coherent-action
  uses (funext extext E-inner action-id action-comp left-unit-coherence right-unit-coherence)
  : has-cocartesian-lifts B E
  := \ b b' u e →
    transport
      ( E b)
      ( \ e → Σ (e' : E b')
      , Σ ( f : dhom B b b' u E e e')
        , is-cocartesian-arrow B b b' u E e e' f)
      ( action (id-hom B b) e)
      ( e)
      ( action-id b e)
      ( lift-action u e 1₂
      , ( \ t → lift-action u e t
      , is-cocartesian-arrow-is-equiv-comp-over-Inner
        B
        E
        E-inner
        u
        ( lift-action u e)
        ( \ a → is-equiv-comp-lift-coherent-action a e)))


```
