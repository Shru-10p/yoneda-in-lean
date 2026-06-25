import YonedaInLean.NatTrans

universe u v u₁ u₂

open Cat NatTrans

/--
A **bijection** between two types
(Defined from scratch because `Equiv` requires Mathlib.)
-/
structure Bijection (α : Type u₁) (β : Type u₂) where
  toFun     : α → β
  invFun    : β → α
  left_inv  : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

namespace Yoneda

variable (C : Category.{u, v})

/--
The **representable presheaf** `Hom(−, A) : Cᵒᵖ ⥤ Type`.
- On objects: `X ↦ C.Hom X A`
- On `f : Cᵒᵖ.Hom X Y` (i.e. `f : C.Hom Y X`): precompose — `g ↦ C.comp f g`
-/
def HomFunctor (A : C.Obj) : C.op ⥤ Type_v.{v} where
  obj X     := C.Hom X A
  map f g   := C.comp f g
  map_id X  := by funext g; exact C.id_comp g
  map_comp {a b c} (f : C.op.Hom a b) (g : C.op.Hom b c) := by
    funext (h : C.Hom a A); exact C.assoc g f h

/--
A morphism `h : C.Hom A B` induces `Hom(−, A) ⟹ Hom(−, B)` by postcomposition:
`(homFunctorMap h)_X(f) = C.comp f h`.
-/
def homFunctorMap {A B : C.Obj} (h : C.Hom A B) :
    HomFunctor C A ⟹ HomFunctor C B where
  app X f             := C.comp f h
  naturality {X Y} k  := by funext f; exact (C.assoc k f h).symm

/-- **φ**: evaluate at `id_A`. -/
private def φ {A : C.Obj} {F : C.op ⥤ Type_v.{v}}
    (α : HomFunctor C A ⟹ F) : F.obj A :=
  α.app A (C.id A)

/-- **ψ**: `ψ(x)_X(f) = F(f)(x)`. -/
private def ψ {A : C.Obj} {F : C.op ⥤ Type_v.{v}}
    (x : F.obj A) : HomFunctor C A ⟹ F where
  app X f               := F.map f x
  naturality {X Y} f    := by
    funext (g : C.Hom X A)
    symm; exact congrFun (F.map_comp (C := C.op) g f) x


/--
**The Yoneda Lemma** — bijection.
-/
def yoneda_bij (A : C.Obj) (F : C.op ⥤ Type_v.{v}) :
    Bijection (HomFunctor C A ⟹ F) (F.obj A) where
  toFun     := φ C
  invFun    := ψ C
  right_inv x := congrFun (F.map_id (C := C.op) A) x
  left_inv  α := by
    apply NatTrans.ext; intro X; funext (f : C.Hom X A)
    show F.map f (α.app A (C.id A)) = α.app X f
    have nat := congrFun (α.naturality (a := A) (b := X) f) (C.id A)
    simp only [HomFunctor, Type_v] at nat
    rw [C.comp_id] at nat
    exact nat

/--
**Naturality in `F`**.

For any `σ : F ⟹ G`, the square
```
  Nat(Hom(−,A), F) ──φ──▶ F(A)
        |                   |
        |                   |
       σ∘−                 σ_A
        |                   |
        v                   v
  Nat(Hom(−,A), G) ──φ──▶ G(A)
```
commutes.
-/
theorem yoneda_natural_F {A : C.Obj} {F G : C.op ⥤ Type_v.{v}}
    (σ : F ⟹ G) (α : HomFunctor C A ⟹ F) :
    σ.app A (φ C α) = φ C (vcomp α σ) :=
  rfl

/--
**Naturality in `A`**.

For any `h : C.Hom A B`, the square
```
  Nat(Hom(−,B), F) ──φ_B──▶ F(B)
        |                    |
        |                    |
      (h∘−)∘−               F(h)
        |                    |
        v                    v
  Nat(Hom(−,A), F) ──φ_A──▶ F(A)
```
commutes.
-/
theorem yoneda_natural_A {A B : C.Obj} (h : C.Hom A B)
    {F : C.op ⥤ Type_v.{v}} (β : HomFunctor C B ⟹ F) :
    F.map h (φ C β) = φ C (vcomp (homFunctorMap C h) β) := by
  show F.map h (β.app B (C.id B)) = β.app A (C.comp (C.id A) h)
  rw [C.id_comp]
  have nat := congrFun (β.naturality (a := B) (b := A) h) (C.id B)
  simp only [HomFunctor, Type_v] at nat
  rw [C.comp_id] at nat
  exact nat

end Yoneda
