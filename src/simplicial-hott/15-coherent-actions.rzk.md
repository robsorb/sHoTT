# Cocartesian families

```rzk
#lang rzk-1
```

## Dependent coslice
```rzk

#section darr-from

#variable B : U
#variable E : B → U

#def darr-from
  ( f : Δ¹ → B)
  ( e : E(f 0₂))
  : U
  := (t : Δ¹) → E (f t) [t ≡ 0₂ ↦ e]

#end darr-from
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

Given a morphism $f : x \to y$ in the base and a start point $e : E(x)$ we can construct a morphism $id_* e \to f_* e$ laying over it.

```rzk
#def lift-action (f : Δ¹ → B) (e : E (f 0₂))
  : darr-from B E f (action (id-hom B (f 0₂)) e)
  := \ t → action (clamp-above B f t) e

```

### Lifts of triangles

Given a triangle in the base and a morphism over the diagonal, we construct a lift of our triangle.

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

The following morphism will be the inverse of post-composition with the constructed lift:

```rzk
#def inv-comp-lift-action uses (action)
  ( a : Δ² → B)
  : ( ( t : Δ¹) → E (comp-Δ² B a t)) → ((t : Δ¹) → E (snd-Δ² B a t))
  := \ h → snd-dΔ² B E a (lift-2-action a h)
```

The following is the same morphism but presented as a sigma type, quantifying over the start point:

```rzk
#def tot-inv-comp-lift-action
  ( a : Δ² → B)
  : ( ( t : Δ¹) → E (comp-Δ² B a t))
  → Σ ( e' : E (a (0₂ , 0₂))) , darr-from B E (snd-Δ² B a) (action (fst-Δ² B a) e')
  := \ h → (h 0₂ , inv-comp-lift-action a h)

```


```rzk
#end lift-action
```
