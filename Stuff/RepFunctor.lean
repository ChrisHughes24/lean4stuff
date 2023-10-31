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
  ( lift_unit : lift R unit = 𝟙 R )

theorem Corepresentation.hom_ext {F : C ⥤ Type u₂}
    {R : Corepresentation F} {X : C} {f g : R.R ⟶ X}
    (h : F.map f R.unit = F.map g R.unit) : f = g := by
  have hf : f = R.lift R.R R.unit ≫ f := by simp [R.lift_unit]
  have hg : g = R.lift R.R R.unit ≫ g := by simp [R.lift_unit]
  rw [hf, hg, map_comp, map_comp, types_comp_apply, map_lift_unit] at h
  simp only [types_comp_apply] at h


def corepresentableOfCorepresentation (F : C ⥤ Type v₁)
   (R : Corepresentation.{u₁, v₁} F) : Corepresentable F :=
  ⟨Opposite.op R.R, ⟨⟨fun X f => F.map f R.unit, by

    simp⟩ , _⟩ ⟩

end CategoryTheory
