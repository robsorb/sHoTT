# Cocartesian families

```rzk
#lang rzk-1
```

```rzk
#assume extext : ExtExt
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

## Horizontal morphisms in a triangle
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

Given a triangle `hom2 B x y z f g h` in the base and a morphism over `h`,
we construct a morphism over `g` that will be the inverse to postcomposition
with the lift over `f`

```rzk
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
```

We can lift the entire triangle to a dependent triangle, which will witness
the right inverse law

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

### The coherence morphism

There is always a dependent morphism `f_* id_* e -> id_* f_* e` in the fiber
over the codomain of `f`, which we call the coherence morphism.

```rzk

#def coherence-morphism-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : hom (E y)
    ( action x y f (action x x (id-hom B x) e))
    ( action y y (id-hom B y) (action x y f e))
  := \ t →
    ( action (f t) y (clamp-below B f t) (action x (f t) (clamp-above B f t) e))

```

### Pushforward of dependent triangles

Any dependent triangle, with bottom edge being the lift induced by the action,
can be pushed forward to a triangle involving, the inverse to composition with
the lift and the coherence morphism.

```rzk

#def action-dhom2-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( g' : dhom B y z g E (action x y f x') z')
  ( h' : dhom B x z h E (action x x (id-hom B x) x') z')
  ( σ' : dhom2 B x y z f g h σ E
    ( action x x (id-hom B x) x')
    ( action x y f x')
    z'
    ( lift-action x y f x')
    g'
    h')
  : dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E
    ( action x y f (action x x (id-hom B x) x'))
    ( action y y (id-hom B y) (action x y f x'))
    ( action z z (id-hom B z) z')
    ( coherence-morphism-action x y f x')
    ( action-id-dhom y z g (action x y f x') z' g')
    ( inv-comp-lift-action x y z f g h σ (action x x (id-hom B x) x') z' h')
  := \ (t , s) →
    action (σ (t , s)) (g s)
      ( clamp-below B (hor-hom-hom2 B x y z f g h σ s) t)
      ( σ' (t , s))

```

## Composing with lifts

Now we will assume that our family is inner

```rzk

#variable is-inner-E
  : is-inner-family B E

```

If `E` is inner we can compose with the lift. We would like to show that this
map is an equivalence.

```rzk

#def comp-lift-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  : dhom B y z g E (action x y f x') z'
  → dhom B x z h E (action x x (id-hom B x) x') z'
  := \ g' → comp-over-is-inner-family B E is-inner-E
    x y z f g h σ
    ( action x x (id-hom B x) x')
    ( action x y f x') z'
    ( lift-action x y f x')
    ( g')

```

We will do this by considering the map on total types

```rzk

#def tot-comp-lift-action uses (is-inner-E)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  :
  ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
  → ( ( t : Δ¹) → E (h t))
  := \ (x' , g') → comp-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t)


#def inv-tot-comp-lift-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  :
  ( ( t : Δ¹) → E (h t))
  → ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
  := \ h' → (h' 0₂ , inv-comp-lift-action x y z f g h σ (h' 0₂) (h' 1₂) h')

```

The lift over our triangle almost witnesses the right inverse law

```rzk

#def comp-lift-action-inv-lift-action-is-action-id-dhom-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : comp-lift-action x y z f g h σ x' (action z z (id-hom B z) z')
    ( inv-comp-lift-action x y z f g h σ x' z' h')
    = action-id-dhom x z h x' z' h'
  := unqiue-comp-over-is-inner-family B E is-inner-E
    x y z f g h σ
    ( action x x (id-hom B x) x')
    ( action x y f x')
    ( action z z (id-hom B z) z')
    ( lift-action x y f x')
    ( inv-comp-lift-action x y z f g h σ x' z' h')
    ( action-id-dhom x z h x' z' h')
    ( lift-2-action x y z f g h σ x' z' h')

```

For the next part of the argument we need to assume that the action is unital

```rzk
#variable is-unital-action :
  ( x : B)
  → ( e : E x)
  → action x x (id-hom B x) e = e
```

Now we can show that our total map has a right inverse

```rzk

#def is-retraction-tot-comp-lift-action uses (is-inner-E action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : tot-comp-lift-action x y z f g h σ
    ( inv-tot-comp-lift-action x y z f g h σ h')
    = h'
  := concat ((t : Δ¹) → E (h t))
    ( tot-comp-lift-action x y z f g h σ
      ( inv-tot-comp-lift-action x y z f g h σ h'))
    ( action-id-dhom x z h x' z' (h'))
    h'
    ( ap
      ( dhom B x z h E (action x x (id-hom B x) x') (action z z (id-hom B z) z'))
      ( ( t : Δ¹) → E (h t))
      ( comp-lift-action x y z f g h σ x' (action z z (id-hom B z) z')
        ( inv-comp-lift-action x y z f g h σ x' z' h'))
      ( action-id-dhom x z h x' z' h')
      ( \ h' → \ t → h' t)
      ( comp-lift-action-inv-lift-action-is-action-id-dhom-action x y z f g h σ x' z' h'))
    ( naiveextext-extext extext
      2
      Δ¹
      ( \ _ → BOT)
      ( \ t → E (h t))
      ( \ _ → recBOT)
      ( action-id-dhom x z h x' z' (h'))
      h'
      ( \ t → is-unital-action (h t) (h' t)))

```

For the left inverse we will need to assume that our action is coherent, in the
sense that the coherence morphism is equal to the following canonical morphism

```rzk

#def zig-zag-hom-unital-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : hom (E y)
    ( action x y f (action x x (id-hom B x) e))
    ( action y y (id-hom B y) (action x y f e))
  :=
  hom-eq (E y)
    ( action x y f (action x x (id-hom B x) e))
    ( action y y (id-hom B y) (action x y f e))
    ( zig-zag-concat (E y)
      ( action x y f (action x x (id-hom B x) e))
      ( action x y f e)
      ( action y y (id-hom B y) (action x y f e))
      ( ap
        ( E x)
        ( E y)
        ( action x x (id-hom B x) e)
        ( e)
        ( action x y f)
        ( is-unital-action x e))
      ( is-unital-action y (action x y f e)))

```

```rzk

#def is-coherent-unital-action uses (is-unital-action)
  : U
  :=
  ( x y : B) → (f : hom B x y) → (e : E x)
  → ( coherence-morphism-action x y f e) = (zig-zag-hom-unital-action x y f e)



```


```rzk
#end lift-action
```
