# Inner families

This is a formalization of important feature of (iso-)inner families. In
particular, we provide an interface for dependent composition, crucially needed
for cocartesian families.

We build on
[Buchholtz and Weinberger (2023), Higher Structures 7, §4](https://doi.org/10.21136/HS.2023.04).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites


```rzk
#assume extext : ExtExt
```




## Dependent arrows
```rzk

#def darr
  ( B : U)
  ( f : Δ¹ → B)
  ( E : B → U)
  : U
  := (t : Δ¹) → E (f t)

#def darr-from
  ( B : U)
  ( f : Δ¹ → B)
  ( E : B → U)
  ( e : E(f 0₂))
  : U
  := (t : Δ¹) → E (f t) [t ≡ 0₂ ↦ e]

```

## Triangles with fixed spine

```rzk

#def dtriangle-with-horn
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : U
  := ((s , t) : Δ²) → E (σ (s , t)) [
    t ≡ 0₂ ↦ f' s
  , s ≡ 1₂ ↦ g' t
  ]

#def diagonal-dtriangle-with-horn
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : dtriangle-with-horn B x y z f g h σ E x' y' z' f' g'
  → dhom B x z h E x' z'
  := \ σ' → \ t → σ' (t , t)

#def forget-diagonal-dhom2
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  ( h' : dhom B x z h E x' z')
  :
  dhom2 B x y z f g h σ E x' y' z' f' g' h'
  → dtriangle-with-horn B x y z f g h σ E x' y' z' f' g'
  := \ σ' → σ'

#def dhom2-dtriangle-with-horn
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  ( σ' : dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
  : dhom2 B x y z f g h σ E x' y' z' f' g'
    ( diagonal-dtriangle-with-horn B x y z f g h σ E x' y' z' f' g' σ')
  := \ t → σ' t

```

### Triangles with fixed spine in terms of sigma types

```rzk

#def dtriangle-with-horn'
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : U
  := Σ (h' : dhom B x z h E x' z') , dhom2 B x y z f g h σ E x' y' z' f' g' h'

```

These two types are equivalent.

```rzk

#def equiv-dtriangle-with-horn-dtriangle-with-horn'
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : Equiv
    ( dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
    ( dtriangle-with-horn' B x y z f g h σ E x' y' z' f' g')
  := equiv-has-inverse
    ( dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
    ( dtriangle-with-horn' B x y z f g h σ E x' y' z' f' g')
    ( \ σ' → (\ t → σ' (t , t) , \ t → σ' t))
    ( \ (h' , σ') → σ')
    ( \ σ' → refl)
    ( \ σ' → refl)

```



### If dependent triangles are equal up to their diagonal, then the diagonals are equal

```rzk
#def eq-dhom-eq-dtriangle-with-horn
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( E : B → U)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  ( h' : dhom B x z h E x' z')
  ( h'' : dhom B x z h E x' z')
  ( σ' : dhom2 B x y z f g h σ E x' y' z' f' g' h')
  ( σ'' : dhom2 B x y z f g h σ E x' y' z' f' g' h'')
  : ( forget-diagonal-dhom2 B x y z f g h σ E x' y' z' f' g' h' σ'
  = forget-diagonal-dhom2 B x y z f g h σ E x' y' z' f' g' h'' σ'')
    → ( h' = h'')
  := ap
    ( dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
    ( dhom B x z h E x' z')
    ( forget-diagonal-dhom2 B x y z f g h σ E x' y' z' f' g' h' σ')
    ( forget-diagonal-dhom2 B x y z f g h σ E x' y' z' f' g' h'' σ'')
    ( diagonal-dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')



```

## Inner families

```rzk
#def is-inner-family
  ( B : U)
  ( E : B → U)
  : U
  := is-right-orthogonal-family
    ( 2 × 2)
    Δ²
    Λ²₁
    B
    E
```

### The relative composition map for morphisms with a fixed domain

```rzk

#section composition-is-inner-family

#variable B : U
#variable E : B → U
#variable is-inner-E : is-inner-family B E
#variables x y z : B
#variable f : hom B x y
#variable g : hom B  y z
#variable h : hom B  x z
#variable σ : hom2 B x y z f g h



#def is-contr-fillers-inner-family
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : is-contr (dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
  := is-inner-E
    σ
    ( \ (s , t) → recOR (t ≡ 0₂ ↦ f' s , s ≡ 1₂ ↦ g' t))

#def is-contr-fillers'-inner-family uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : is-contr (dtriangle-with-horn' B x y z f g h σ E x' y' z' f' g')
  := is-contr-equiv-is-contr
    ( dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
    ( dtriangle-with-horn' B x y z f g h σ E x' y' z' f' g')
    ( equiv-dtriangle-with-horn-dtriangle-with-horn' B x y z f g h σ
      E x' y' z' f' g')
    ( is-contr-fillers-inner-family x' y' z' f' g')

#def fill-over-is-inner-family uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : dtriangle-with-horn B x y z f g h σ E x' y' z' f' g'
  :=
    center-contraction
      ( dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
      ( is-contr-fillers-inner-family x' y' z' f' g')

#def comp-over-is-inner-family uses (is-inner-E σ)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  :
  ( dhom B x y f E x' y')
  → ( dhom B y z g E y' z')
  → ( dhom B x z h E x' z')
  := \ f' g' t → fill-over-is-inner-family x' y' z' f' g' (t , t)

#def fill-over-is-inner-family' uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  : dhom2 B x y z f g h σ E x' y' z'
    f'
    g'
    ( comp-over-is-inner-family x' y' z' f' g')
  := \ t → fill-over-is-inner-family x' y' z' f' g' t

```

### Dependent triangles witness equality for inner families

```rzk

#def unqiue-fill-over-is-inner-family uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  ( σ' : dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
  : fill-over-is-inner-family x' y' z' f' g' = σ'
  := homotopy-contraction
    ( dtriangle-with-horn B x y z f g h σ E x' y' z' f' g')
    ( is-contr-fillers-inner-family x' y' z' f' g')
    σ'

#def unqiue-comp-over-is-inner-family uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  ( h' : dhom B x z h E x' z')
  :
  dhom2 B x y z f g h σ E x' y' z' f' g' h'
  → ( comp-over-is-inner-family x' y' z' f' g') = h'
  := \ σ' →
    eq-dhom-eq-dtriangle-with-horn B x y z f g h σ E x' y' z' f' g'
      ( comp-over-is-inner-family x' y' z' f' g')
      ( h')
      ( dhom2-dtriangle-with-horn B x y z f g h σ E x' y' z' f' g'
        ( fill-over-is-inner-family x' y' z' f' g'))
      ( σ')
      ( unqiue-fill-over-is-inner-family x' y' z' f' g'
        ( forget-diagonal-dhom2 B x y z f g h σ E x' y' z' f' g' h' σ'))


#def equiv-eq-dhom2-is-inner-family uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( g' : dhom B y z g E y' z')
  ( h' : dhom B x z h E x' z')
  : Equiv
    ( comp-over-is-inner-family x' y' z' f' g' = h')
    ( dhom2 B x y z f g h σ E x' y' z' f' g' h')
  :=
  second
    ( first
      ( fundamental-theorem-of-identity-types
        ( dhom B x z h E x' z')
        ( \ h' → dhom2 B x y z f g h σ E x' y' z' f' g' h'))
      ( is-contr-fillers'-inner-family x' y' z' f' g'))
    ( h')


#def equiv-fib-comp-tot-dhom2 uses (is-inner-E)
  ( x' : E x)
  ( y' : E y)
  ( z' : E z)
  ( f' : dhom B x y f E x' y')
  ( h' : dhom B x z h E x' z')
  : Equiv
    ( fib
      ( dhom B y z g E y' z')
      ( dhom B x z h E x' z')
      ( comp-over-is-inner-family x' y' z' f')
      ( h'))
    ( Σ ( g' : dhom B y z g E y' z')
    , dhom2 B x y z f g h σ E x' y' z' f' g' h')
  :=
  total-equiv-family-of-equiv
    ( dhom B y z g E y' z')
    ( \ g' → comp-over-is-inner-family x' y' z' f' g' = h')
    ( \ g' → dhom2 B x y z f g h σ E x' y' z' f' g' h')
    ( \ g' → equiv-eq-dhom2-is-inner-family x' y' z' f' g' h')

#end composition-is-inner-family

```

#### Dependent triangles with one degenerate edge induce equalities of dependent homs

```rzk

#def eq-dhom-dhom2-id-hom-inner-family
  ( B : U)
  ( E : B → U)
  ( is-inner-E : is-inner-family B E)
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  ( f' : dhom B x y f E x' y')
  ( f'' : dhom B x y f E x' y')
  : dhom2 B x x y (id-hom B x) f f (id-comp-witness B x y f) E x' x' y'
    ( id-hom (E x) x')
    f''
    f'
  → f' = f''
  :=
  \ σ' →
    eq-dhom-eq-dtriangle-with-horn
      B x x y (id-hom B x) f f (id-comp-witness B x y f)
      E x' x' y' (id-hom (E x) x') f''
      f'
      f''
      σ'
      ( \ (t , s) → f'' s)
      ( all-elements-equal-is-contr
        ( dtriangle-with-horn B x x y (id-hom B x) f f (id-comp-witness B x y f)
          E x' x' y' (id-hom (E x) x') f'')
        ( is-contr-fillers-inner-family B E is-inner-E
          x x y (id-hom B x) f f (id-comp-witness B x y f)
          x' x' y' (id-hom (E x) x') f'')
        σ'
        ( \ (t , s) → f'' s))

```

#### Utilities

This is a special lemma used in the coherent actions proof

```rzk

#def eq-pullback-dom-projection-dhom2-ext-homotopy-inner-family
  ( B : U)
  ( E : B → U)
  ( is-inner-E : is-inner-family B E)
  ( x y z : B)
  ( g : hom B y z)
  ( x' x'' : E x)
  ( z'' : E z)
  ( p : x' = x'')
  ( F : E x → E y)
  ( g'' : (t : Δ¹) → E (g t))
  ( g' : dhom B y z g E (F x'') z'')
  ( H : (t : Δ¹) → g'' t =_{E (g t)} g' t)
  :
  ( h' : dhom B y z g E (F x') (g'' 1₂))
  → ( dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E (F x') (g'' 0₂) (g'' 1₂)
    ( hom-eq (E y) (F x') (g'' 0₂)
      ( zig-zag-concat (E y)
        ( F x')
        ( F x'')
        ( g'' 0₂)
        ( ap (E x) (E y) (x') (x'') F p)
        ( H 0₂)))
    g''
    h'
  )
  → ( x' , h') =_{Σ (e : E x) , darr-from B g E (F e)} (x'' , g')
  :=
  ind-ext-htpy-end extext 2 Δ¹ (\ _ → BOT) (\ t → E (g t)) (\ _ → recBOT)
    g'
    ( \ g'' H →
      ( h' : dhom B y z g E (F x') (g'' 1₂))
    → ( dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E (F x') (g'' 0₂) (g'' 1₂)
        ( hom-eq (E y) (F x') (g'' 0₂)
          ( zig-zag-concat (E y)
            ( F x')
            ( F x'')
            ( g'' 0₂)
            ( ap (E x) (E y) (x') (x'') F p)
            ( H 0₂)))
        g''
        h'
      )
      → ( x' , h') =_{Σ (e : E x) , darr-from B g E (F e)} (x'' , g'))
    ( \ h' σ' →
      ind-path
        ( E x)
        x'
        ( \ x'' p →
          ( g' : dhom B y z g E (F x'') z'')
        → ( dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E
            ( F x') (F x'') (z'')
            ( hom-eq (E y) (F x') (F x'') (ap (E x) (E y) x' x'' F p))
            g'
            h')
          → ( x' , h') =_{Σ (e : E x) , darr-from B g E (F e)} (x'' , g'))
        ( \ g' σ' →
          ap
            ( dhom B y z g E (F x') z'')
            ( Σ ( e : E x) , darr-from B g E (F e))
            h'
            g'
            ( \ k → (x' , k))
            ( eq-dhom-dhom2-id-hom-inner-family B E is-inner-E
              y z g
              ( F x') (z'')
              h'
              g'
              σ'))
        x'' p
        g' σ')
    g'' H

```



## Iso-Inner families

```rzk
#def is-isoinner-family
  ( B : U)
  ( E : B → U)
  : U
  := product
    ( is-inner-family B E)
    ( ( b : B) → is-rezk (E b))

```
