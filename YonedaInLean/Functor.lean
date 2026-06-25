import YonedaInLean.Category

universe u v u' v'

namespace Cat -- namespace to avoid collision with Lean's built-in `Functor`

structure Functor (C : Category.{u, v}) (D : Category.{u', v'}) where
  obj      : C.Obj → D.Obj
  map      : {a b : C.Obj} → C.Hom a b → D.Hom (obj a) (obj b)
  map_id   : (a : C.Obj) → map (C.id a) = D.id (obj a)
  map_comp : {a b c : C.Obj} → (f : C.Hom a b) → (g : C.Hom b c) → map (C.comp f g) = D.comp (map f) (map g)

-- Notation
infixr:26 " ⥤ " => Cat.Functor

-- The identity functor
def Functor.id (C : Category.{u, v}) : C ⥤ C where
  obj a        := a
  map f        := f
  map_id _     := rfl
  map_comp _ _ := rfl

-- Composition of functors.
def Functor.comp {C : Category.{u, v}} {D : Category.{u', v'}} {E : Category}
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj a        := G.obj (F.obj a)
  map f        := G.map (F.map f)
  map_id a     := by rw [F.map_id, G.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp]

/--
The category of **types** (in universe `v`) and
morphisms are functions.
This serves as the "target" for presheaves (`F : Cᵒᵖ ⥤ Type_v`.)
-/
def Type_v: Category.{v+1, v} where
  Obj        := Type v
  Hom a b    := a → b
  id _       := fun x => x
  comp f g   := fun x => g (f x)
  id_comp _  := rfl
  comp_id _  := rfl
  assoc _ _ _ := rfl

end Cat
