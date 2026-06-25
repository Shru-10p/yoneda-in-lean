import YonedaInLean.Functor

universe u v u' v'

open Cat

-- A natural transformation between two functors `F` and `G`.
structure NatTrans {C : Category.{u, v}} {D : Category.{u', v'}}
    (F G : C ⥤ D) where
  app        : (a : C.Obj) → D.Hom (F.obj a) (G.obj a)
  naturality : {a b : C.Obj} → (f : C.Hom a b) → D.comp (app a) (G.map f) = D.comp (F.map f) (app b)

namespace NatTrans

-- Notation
infixr:25 " ⟹ " => NatTrans

-- The identity natural transformation
def id {C : Category.{u, v}} {D : Category.{u', v'}} (F : C ⥤ D) : F ⟹ F where
  app a      := D.id (F.obj a)
  naturality f := by
    rw [D.id_comp, D.comp_id]

/--
Vertical composition of natural transformations.

Given functors `F G H : C ⥤ D` and natural transformations
`α : F ⟹ G ` and  `β : G ⟹ H`, for any object `a` in category `C` we obtain the comutative diagram

```
  F(a) ----F(f)----> F(b)
   |                  |
  α_a                α_b          ← naturality of α:  α_a ≫ G(f) = F(f) ≫ α_b
   |                  |
   v                  v
  G(a) ----G(f)----> G(b)
   |                  |
  β_a                β_b          ← naturality of β:  β_a ≫ H(f) = G(f) ≫ β_b
   |                  |
   v                  v
  H(a) ----H(f)----> H(b)
```

Pasting the two squares gives the outer rectangle for the composite `β ∘ α`:

```
  F(a) ----F(f)----> F(b)
   |                  |
β_a∘α_a            β_b∘α_b        ← naturality of (β∘α): β_a∘α_a ≫ H(f) = F(f) ≫ β_b∘α_b
   |                  |
   v                  v
  H(a) ----H(f)----> H(b)
```

The component at each `a` is `D.comp (α.app a) (β.app a)`.
-/
def vcomp {C : Category.{u, v}} {D : Category.{u', v'}}
    {F G H : C ⥤ D} (α : F ⟹ G) (β : G ⟹ H) : F ⟹ H where
  app a      := D.comp (α.app a) (β.app a)
  naturality {a b} f := by
    rw [D.assoc (α.app a) (β.app a) (H.map f)]
    rw [β.naturality f]
    rw [← D.assoc (α.app a) (G.map f) (β.app b)]
    rw [α.naturality f]
    rw [D.assoc (F.map f) (α.app b) (β.app b)]

-- Thm: Two natural transformations are equal iff all their components are equal
@[ext]
theorem ext {C : Category.{u, v}} {D : Category.{u', v'}}
    {F G : C ⥤ D} {α β : F ⟹ G}
    (h : ∀ a, α.app a = β.app a) : α = β := by
  obtain ⟨appα, _⟩ := α
  obtain ⟨appβ, _⟩ := β
  congr 1
  funext a
  exact h a

end NatTrans
