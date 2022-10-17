import Stuff.normalizing_properly.category

structure free_cat : Type :=
( toString : String )
deriving DecidableEq

namespace free_cat

inductive hom : (X Y : free_cat) → Type
| id (X : free_cat) : hom X X
| comp' (X Y Z : free_cat)
  (f : hom X Y) (g : String) : hom X Z

instance hom.DecidableEq : {X Y : free_cat} → DecidableEq (hom X Y)
| _, _, hom.id _, hom.id _ => isTrue rfl
| _, _, hom.comp' _ Y _ f₁ g₁, hom.comp' _ Y' _ f₂ g₂ =>
  if hY : Y = Y'
    then by
      subst hY
      exact if hg : g₁ = g₂
        then by
          subst hg
          exact @decidable_of_decidable_of_iff (f₁ = f₂) _ (hom.DecidableEq _ _)
            (by
              apply Iff.intro
              { intro h; rw [h] }
              { intro h; injection h; assumption })
        else isFalse (λ h => by injection h; contradiction)
    else isFalse (λ h => by injection h; contradiction)
| _, _, hom.id _, hom.comp' _ _ _ _ _ => isFalse (λ h => by injection h)
| _, _, hom.comp' _ _ _ _ _, hom.id _ => isFalse (λ h => by injection h)

def mh (X Y : free_cat) (s : String) : hom X Y :=
hom.comp' X X Y (hom.id X) s

def hom.comp : {X Y Z : free_cat} →
  hom X Y → hom Y Z → hom X Z
| _, _, _, f, hom.id _ => f
| _, _, _, f, hom.comp' _ _ _ g h =>
  hom.comp' _ _ _ (comp f g) h

private theorem id_comp : {X Y : free_cat} → (f : hom X Y) →
  (hom.id X).comp f = f
| _, _, hom.id _ => rfl
| _, _, hom.comp' _ _ _ f g => by
rw [hom.comp, id_comp f]

private theorem assoc : {W X Y Z : free_cat} → (f : hom W X) →
  (g : hom X Y) → (h : hom Y Z) →
  (f.comp g).comp h = f.comp (g.comp h)
| _, _, _, _, f, g, hom.id _ => rfl
| _, _, _, _, f, g, hom.comp' _ _ _ h i => by
rw [hom.comp, assoc f g h, hom.comp, hom.comp]

instance : category free_cat :=
{ hom := hom,
  id := hom.id,
  comp := hom.comp,
  id_comp := id_comp,
  comp_id := λ _ => rfl,
  assoc := assoc }

instance {X Y : free_cat} : DecidableEq (X ⟶ Y) :=
hom.DecidableEq

end free_cat