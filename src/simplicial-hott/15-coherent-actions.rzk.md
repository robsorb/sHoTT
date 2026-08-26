# Cocartesian families

```rzk
#lang rzk-1
```



## Clamping morphisms

```rzk
#section clamping

#variable B : U


#def clamp (f : Δ¹ → B) ((u , l) : Δ²)
  : hom B (f l) (f u)
  := \ t →
    recOR (t ≤ l ↦ f l , l ≤ t ↦
      recOR (u ≤ t ↦ f u , t ≤ u ↦ f t))

#def clamp-above
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : hom B (f 0₂) (f t)
  := clamp f (t , 0₂)

#def clamp-below
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : hom B (f t) (f 1₂)
  := clamp f (1₂ , t)

#def clamp-commutes
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : hom2 B (f 0₂) (f t) (f 1₂) (clamp-above f t) (clamp-below f t) f
  := \ (x , y) → clamp f (x , y) t

#variable E : B → U

#def dclamp
  ( f : Δ¹ → B)
  ( g : (t : Δ¹) → E (f t))
  ( ( u , l) : Δ²)
  : dhom B (f l) (f u) (clamp f (u , l)) E (g l) (g u)
  := \ t →
    recOR (t ≤ l ↦ g l , l ≤ t ↦
      recOR (u ≤ t ↦ g u , t ≤ u ↦ g t))

#end clamping
```

## Horizontal morpihsms in a triangle
```rzk

#def hor-hom-hom2
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( t : Δ¹)
  : hom B (h t) (g t)
  := \ s →
    recOR (
      s ≤ t ↦ h t
      , t ≤ s ↦ σ (s , t)
    )

```



## Lifts from transport

```rzk

#section lift-action

#variable B : U
#variable E : B → U
#variable action : (x y : B) → hom B x y → E x → E y
```

### Lifts of edges

Given a morphism $f : x \to y$ in the base and a start point $e : E(x)$ we can
construct a morphism $id_* e \to f_* e$ laying over it.

```rzk


#def lift-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom B x y f E (action x x (id-hom B x) e) (action x y f e)
  := \ t → action x (f t) (clamp-above B f t) e

```

### Lifts of triangles

Given a triangle in the base and a morphism over the diagonal, we construct a
lift of our triangle.

```rzk

#def action-id-dhom
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  ( f' : dhom B x y f E x' y')
  : dhom B x y f E
    ( action x x (id-hom B x) x')
    ( action y y (id-hom B y) y')
  := \ t → action (f t) (f t) (id-hom B (f t)) (f' t)

#def inv-comp-lift-action uses (action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : dhom B y z g E
    ( action x y f x')
    ( action z z (id-hom B z) z')
  := \ t → action (h t) (g t) (hor-hom-hom2 B x y z f g h σ t) (h' t)

#def lift-2-action uses (action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : dhom2 B x y z f g h σ E
    ( action x x (id-hom B x) x')
    ( action x y f x')
    ( action z z (id-hom B z) z')
    ( lift-action x y f x')
    ( inv-comp-lift-action x y z f g h σ x' z' h')
    ( action-id-dhom x z h x' z' h')
  := \ (s , t) →
    lift-action
      ( h t) (g t) (hor-hom-hom2 B x y z f g h σ t)
      ( h' t) s

```

The following morphism will be the inverse of post-composition with the
constructed lift:

```rzk
-- #def inv-comp-lift-action uses (action)
--   ( a : Δ² → B)
--   : ( ( t : Δ¹) → E (comp-Δ² B a t)) → ((t : Δ¹) → E (snd-Δ² B a t))
--   := \ h → snd-dΔ² B E a (lift-2-action a h)
```

The following is the same morphism but presented as a sigma type, quantifying
over the start point:

```rzk
-- #def tot-inv-comp-lift-action
--   ( a : Δ² → B)
--   : ( ( t : Δ¹) → E (comp-Δ² B a t))
--   → Σ ( e' : E (a (0₂ , 0₂))) , darr-from B (snd-Δ² B a) E (action (fst-Δ² B a) e')
--   := \ h → (h 0₂ , inv-comp-lift-action a h)

```


```rzk
#end lift-action
```
