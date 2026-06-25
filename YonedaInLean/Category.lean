/-!

A category `C` consists of:
- A type of objects `Obj`
- For each pair of objects `a b : Obj`, a type of morphisms `Hom a b`
- An identity morphism `id a : Hom a a` for each object `a`
- Composition `comp f g : Hom a c` for `f : Hom a b`, `g : Hom b c`
- Associativity and identity laws for composition.

A category `C` is called **locally small** if `C.Hom a b` is a type in
some fixed universe (`v` in this case) for all objects `a b : C.Obj`.
-/

universe u v

-- A locally small category.
structure Category where
  Obj   : Type u
  Hom   : Obj → Obj → Type v
  id    : (a : Obj) → Hom a a
  comp  : {a b c : Obj} → Hom a b → Hom b c → Hom a c -- We write `comp f g` for `g∘f` (diagrammatic order)
  id_comp : {a b : Obj} → (f : Hom a b) → comp (id a) f = f
  comp_id : {a b : Obj} → (f : Hom a b) → comp f (id b) = f
  assoc : {a b c d : Obj} → (f : Hom a b) → (g : Hom b c) → (h : Hom c d)
        → comp (comp f g) h = comp f (comp g h)

namespace Category

-- The opposite category `Cᵒᵖ`
def op (C : Category.{u, v}) : Category.{u, v} where
  Obj        := C.Obj
  Hom a b    := C.Hom b a -- morphisms reversed
  id a       := C.id a
  comp f g   := C.comp g f -- composition reversed
  id_comp f  := C.comp_id f
  comp_id f  := C.id_comp f
  assoc f g h := (C.assoc h g f).symm

-- Notation
postfix:max "ᵒᵖ" => Category.op

end Category
