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



## Lifts from transport

```rzk

#section lift-action

#variable B : U
#variable E : B → U
#variable action : (f : Δ¹ → B) → E (f 0₂) → E (f 1₂)
```

### Lifts of edges

Given a morphism $f : x \to y$ in the base and a start point $e : E(x)$ we can
construct a morphism $id_* e \to f_* e$ laying over it.

```rzk
#def lift-action (f : Δ¹ → B) (e : E (f 0₂))
  : darr-from B f E (action (id-hom B (f 0₂)) e)
  := \ t → action (clamp-above B f t) e

```

### Lifts of triangles

Given a triangle in the base and a morphism over the diagonal, we construct a
lift of our triangle.

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

The following morphism will be the inverse of post-composition with the
constructed lift:

```rzk
#def inv-comp-lift-action uses (action)
  ( a : Δ² → B)
  : ( ( t : Δ¹) → E (comp-Δ² B a t)) → ((t : Δ¹) → E (snd-Δ² B a t))
  := \ h → snd-dΔ² B E a (lift-2-action a h)
```

The following is the same morphism but presented as a sigma type, quantifying
over the start point:

```rzk
#def tot-inv-comp-lift-action
  ( a : Δ² → B)
  : ( ( t : Δ¹) → E (comp-Δ² B a t))
  → Σ ( e' : E (a (0₂ , 0₂))) , darr-from B (snd-Δ² B a) E (action (fst-Δ² B a) e')
  := \ h → (h 0₂ , inv-comp-lift-action a h)

```

### Pushforward of dependent triangles

Given a dependent triangle we can push it forward along the horizontal morphisms
of the triangle in the base to obtain a dependent triangle laying over the
second edge in the bottom triangle.

```rzk
#def action-dtriangle
  ( a : Δ² → B)
  ( da : (t : Δ²) → E (a t))
  : ( ( x , y) : Δ²) → E (snd-Δ² B a y)
  := \ (x , y) → action (clamp-below B (hor-edge-Δ² B a y) x) (da (x , y))

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
-- #variables inner-E : is-inner-family B E


-- #def comp-lift-action
--   ( a : Δ² → B)
--   ( e : E (a (0₂ , 0₂)))
--   : ( darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
--   → ( darr-from B E (comp-Δ² B a) (action (id-hom B (a (0₂ , 0₂))) e))
--   := \ g →
--     comp-over-Inner B E E-inner
--       a
--       ( lift-action (fst-Δ² B a) e)
--       g

-- #def fill-lift-action
--   ( a : Δ² → B)
--   ( e : E (a (0₂ , 0₂)))
--   ( g : darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
--   : ( t : Δ²) → E (a t)
--   := fill-over-Inner B E
--     E-inner
--     a
--     ( lift-action (fst-Δ² B a) e)
--     g

-- #def fst-fill-lift uses (E-inner)
--   ( a : Δ² → B)
--   ( e : E (a (0₂ , 0₂)))
--   ( g : darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e))
--   : fst-dΔ² B E a (fill-lift-action a e g) = (lift-action (fst-Δ² B a) e)
--   := refl
```




```rzk
#end lift-action
```
