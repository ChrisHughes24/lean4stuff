import Stuff.normalizing_properly.category

structure free_cat : Type :=
( toString : String )

namespace free_cat

inductive hom : (X Y : free_cat) → Type
| id (X : free_cat) : hom X X
| comp' (X Y Z : free_cat)
  (f : hom X Y) (g : String) : hom X Z

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

end free_cat