import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]

structure Corepresentation (F : C ⥤ Type u₂) :=
  ( R : C )
  ( lift : ∀ X : C, F.obj X → (R ⟶ X))
  ( unit : F.obj R )
  ( map_lift_unit : ∀ (X : C) (f : F.obj X), F.map (lift X f) unit = f )
  ( lift_unit : ∀ (X : C) (f : R ⟶ X), lift X (F.map f unit) = f )

@[ext]
theorem Corepresentation.hom_ext {F : C ⥤ Type u₂}
    {R : Corepresentation F} {X : C} {f g : R.R ⟶ X}
    (h : F.map f R.unit = F.map g R.unit) : f = g := by
  rw [← R.lift_unit _ f, h, R.lift_unit]

def corepresentableOfCorepresentation (F : C ⥤ Type v₁)
   (R : Corepresentation.{u₁, v₁} F) : Corepresentable F :=
  ⟨Opposite.op R.R, ⟨⟨fun X f => F.map f R.unit, by aesop_cat⟩,
    ⟨⟨⟨R.lift, by
      intros
      ext
      apply Corepresentation.hom_ext
      simp [R.map_lift_unit]⟩, by
      ext
      simp [R.lift_unit], by
      ext
      simp [R.map_lift_unit]⟩⟩⟩⟩

end CategoryTheory
