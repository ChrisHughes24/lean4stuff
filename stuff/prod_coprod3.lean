
class category (C : Type) :=
( hom : C → C → Type )
( id : (X : C) → hom X X )
( comp : {X Y Z : C} → hom X Y → hom Y Z → hom X Z )
( id_comp {X Y : C} (f : hom X Y) : comp (id X) f = f )
( comp_id {X Y : C} (f : hom X Y) : comp f (id Y) = f )
( assoc {W X Y Z : C} (f : hom W X) (g : hom X Y) (h : hom Y Z) :
    comp (comp f g) h = comp f (comp g h) )

notation " 𝟙 " => category.id
infixr: 80 " ≫ " => category.comp
infixr: 10 " ⟶ " => category.hom

variable (C : Type) [category C]

inductive prod_coprod : Type
| of_cat' : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod

variable {C}

namespace prod_coprod

@[simp] def size : prod_coprod C → Nat
| of_cat' _ => 1
| prod X Y => size X + size Y + 1
| coprod X Y => size X + size Y + 1

inductive syn : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} : (X ⟶ Y) → syn (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} : syn X Y → syn X Z → syn X (Y.prod Z)
| fst {X Y : prod_coprod C} : syn (X.prod Y) X
| snd {X Y : prod_coprod C} : syn (X.prod Y) Y
| coprod_mk {X Y Z : prod_coprod C} : syn X Z → syn Y Z → syn (X.coprod Y) Z
| inl {X Y : prod_coprod C} : syn X (X.coprod Y)
| inr {X Y : prod_coprod C} : syn Y (X.coprod Y)
| id (X : prod_coprod C) : syn X X
| comp {X Y Z : prod_coprod C} : syn X Y → syn Y Z → syn X Z

namespace syn

inductive rel : {X Y : prod_coprod C} → syn X Y → syn X Y → Prop
| refl {X Y : prod_coprod C} (f : syn X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : syn X Y} : rel f g → rel g f
| trans {X Y : prod_coprod C} {f g h : syn X Y} : rel f g → rel g h → rel f h
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : syn X Y} {g₁ g₂ : syn Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : syn X Y} {g₁ g₂ : syn X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : syn X Z} {g₁ g₂ : syn Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| id_comp {X Y : prod_coprod C} (f : syn X Y) : rel ((syn.id X).comp f) f
| comp_id {X Y : prod_coprod C} (f : syn X Y) : rel (f.comp (syn.id Y)) f
| assoc {W X Y Z : prod_coprod C} (f : syn W X) (g : syn X Y) (h : syn Y Z) :
  rel ((f.comp g).comp h) (f.comp (g.comp h))
| of_cat_id {X : C} : rel (syn.of_cat (𝟙 X)) (syn.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (syn.of_cat (f ≫ g)) (syn.comp (syn.of_cat f) (syn.of_cat g))
| mk_fst_comp {X Y Z : prod_coprod C} (f : syn X Y) (g : syn X Z) :
  rel (syn.comp (syn.prod_mk f g) syn.fst) f
| mk_snd_comp {X Y Z : prod_coprod C} (f : syn X Y) (g : syn X Z) :
  rel (syn.comp (syn.prod_mk f g) syn.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : syn X (Y.prod Z)) :
  rel (syn.prod_mk (f.comp syn.fst) (f.comp syn.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : syn X Z) (g : syn Y Z) :
  rel (syn.comp syn.inl (syn.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : syn X Z) (g : syn Y Z) :
  rel (syn.comp syn.inr (syn.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : syn (X.coprod Y) Z) :
  rel (syn.coprod_mk (syn.inl.comp f) (syn.inr.comp f)) f

infixl:50 " ♥ " => rel

instance : Trans (@rel C _ X Y) (@rel C _ X Y) (@rel C _ X Y) where
  trans := rel.trans

theorem rel_prod {X Y Z : prod_coprod C} {f g : syn X (Y.prod Z)}
  (h₁ : rel (f.comp syn.fst) (g.comp syn.fst))
  (h₂ : rel (f.comp syn.snd) (g.comp syn.snd)) :
  rel f g :=
rel.trans (rel.symm (rel.prod_eta f)) (rel.trans (rel.prod_mk_congr h₁ h₂) (rel.prod_eta g))

theorem rel_coprod {X Y Z : prod_coprod C} {f g : syn (X.coprod Y) Z}
  (h₁ : rel (syn.inl.comp f) (syn.inl.comp g))
  (h₂ : rel (syn.inr.comp f) (syn.inr.comp g)) :
  rel f g :=
rel.trans (rel.symm (rel.coprod_eta f)) (rel.trans (rel.coprod_mk_congr h₁ h₂) (rel.coprod_eta g))

end syn

inductive norm_hom : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} (f : X ⟶ Y) : norm_hom (of_cat' X) (of_cat' Y)
| coprod_mk {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z) :
  norm_hom (X.coprod Y) Z
| prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  norm_hom X (prod Y Z)
| comp_inl {X Y Z : prod_coprod C} (f : norm_hom X Y) :
  norm_hom X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : norm_hom X Z) :
  norm_hom X (coprod Y Z)
| fst_comp {X Y Z : prod_coprod C} (f : norm_hom X Z) :
  norm_hom (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : norm_hom Y Z) :
  norm_hom (prod X Y) Z

namespace norm_hom

inductive rel : {X Y : prod_coprod C} → norm_hom X Y → norm_hom X Y → Prop
| refl {X Y : prod_coprod C} (f : norm_hom X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : norm_hom X Y} : rel g f → rel f g
| trans {X Y : prod_coprod C} {f g h : norm_hom X Y} : rel f g → rel g h → rel f h
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom X Z} {g₁ g₂ : norm_hom Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (coprod_mk f₁ g₁) (coprod_mk f₂ g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom X Y} {g₁ g₂ : norm_hom X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (prod_mk f₁ g₁) (prod_mk f₂ g₂)
| comp_inl_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom X Y} :
  rel f₁ f₂ → rel (comp_inl f₁ : norm_hom X (coprod Y Z)) (comp_inl f₂)
| comp_inr_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom X Z} :
  rel f₁ f₂ → rel (comp_inr f₁ : norm_hom X (coprod Y Z)) (comp_inr f₂)
| fst_comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom X Z} :
  rel f₁ f₂ → rel (fst_comp f₁ : norm_hom (prod X Y) Z) (fst_comp f₂)
| snd_comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom Y Z} :
  rel f₁ f₂ → rel (snd_comp f₁ : norm_hom (prod X Y) Z) (snd_comp f₂)
| fst_comp_prod_mk {W X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  rel (fst_comp (prod_mk f g) : norm_hom (prod X W) (prod Y Z)) (prod_mk f.fst_comp g.fst_comp)
| snd_comp_prod_mk {W X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  rel (snd_comp (prod_mk f g) : norm_hom (prod W X) (prod Y Z)) (prod_mk f.snd_comp g.snd_comp)
| comp_inl_coprod_mk {W X Y Z : prod_coprod C} (f : norm_hom W Y) (g : norm_hom X Y) :
  rel (comp_inl (coprod_mk f g) : norm_hom (coprod W X) (coprod Y Z))
    (coprod_mk f.comp_inl g.comp_inl)
| comp_inr_coprod_mk {W X Y Z : prod_coprod C} (f : norm_hom W Y) (g : norm_hom X Y) :
  rel (comp_inr (coprod_mk f g) : norm_hom (coprod W X) (coprod Z Y))
    (coprod_mk f.comp_inr g.comp_inr)
| fst_comp_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom W Y) :
  rel (f.fst_comp.comp_inl : norm_hom (prod W X) (coprod Y Z)) f.comp_inl.fst_comp
| snd_comp_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom X Y) :
  rel (f.snd_comp.comp_inl : norm_hom (prod W X) (coprod Y Z)) f.comp_inl.snd_comp
| fst_comp_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom W Z) :
  rel (f.fst_comp.comp_inr : norm_hom (prod W X) (coprod Y Z)) f.comp_inr.fst_comp
| snd_comp_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom X Z) :
  rel (f.snd_comp.comp_inr : norm_hom (prod W X) (coprod Y Z)) f.comp_inr.snd_comp

def to_inj : {X Y Z : prod_coprod C} → (f : norm_hom X (coprod Y Z)) →
  Option ((norm_hom X Y) ⊕ (norm_hom X Z))
| _, _, _, comp_inl f => some (Sum.inl f)
| _, _, _, comp_inr f => some (Sum.inr f)
| _, _, _, fst_comp f =>
  match to_inj f with
  | none => none
  | some (Sum.inl f) => some (Sum.inl (fst_comp f))
  | some (Sum.inr f) => some (Sum.inr (fst_comp f))
| _, _, _, snd_comp f =>
  match to_inj f with
  | none => none
  | some (Sum.inl f) => some (Sum.inl (snd_comp f))
  | some (Sum.inr f) => some (Sum.inr (snd_comp f))
| _, _, _, coprod_mk f g =>
  match to_inj f, to_inj g with
  | some (Sum.inl f), some (Sum.inl g) => some (Sum.inl (coprod_mk f g))
  | some (Sum.inr f), some (Sum.inr g) => some (Sum.inr (coprod_mk f g))
  | _, _ => none

theorem to_inj_eq_inl : {X Y Z : prod_coprod C} → {f : norm_hom X (coprod Y Z)} →
  {g : norm_hom X Y} → to_inj f = some (Sum.inl g) → rel f g.comp_inl
| _, _, _, comp_inl f, g, h => by
  simp [to_inj] at h
  simp [h]
  exact rel.refl _
  | _, _, _, comp_inr f, g, h => by
  simp [to_inj] at h
| _, _, _, snd_comp f, g, h =>
  have hi : ∃ i, to_inj f = some (Sum.inl i) := by
  { simp [to_inj] at h
    revert h
    match to_inj f with
    | some (Sum.inl i) => intro h; exact ⟨i, rfl⟩
    | some (Sum.inr _) => simp
    | none => simp }
  match hi with
  | ⟨i, hi⟩ => by
  simp [hi, to_inj] at h
  rw [← h]
  exact rel.trans (rel.snd_comp_congr (to_inj_eq_inl hi))
    (rel.snd_comp_comp_inl i).symm
| _, _, _, fst_comp f, g, h =>
  have hi : ∃ i, to_inj f = some (Sum.inl i) := by
  { simp [to_inj] at h
    revert h
    match to_inj f with
    | some (Sum.inl i) => intro h; exact ⟨i, rfl⟩
    | some (Sum.inr _) => simp
    | none => simp }
  match hi with
  | ⟨i, hi⟩ => by
  simp [hi, to_inj] at h
  rw [← h]
  exact rel.trans (rel.fst_comp_congr (to_inj_eq_inl hi))
    (rel.fst_comp_comp_inl i).symm
| _, _, _, coprod_mk f g, i, h =>
  have hi : ∃ f' g', to_inj f = some (Sum.inl f') ∧ to_inj g = some (Sum.inl g') := by
  { simp [to_inj] at h
    revert h
    match to_inj f, to_inj g with
    | some (Sum.inl f'), some (Sum.inl g') => intro h; exact ⟨f', g', rfl, rfl⟩
    | some (Sum.inr _), some (Sum.inr _) => simp
    | none, _ => simp
    | _, none => simp
    | some (Sum.inl _), some (Sum.inr _) => simp
    | some (Sum.inr _), some (Sum.inl _) => simp }
  match hi with
  | ⟨f', g', hf, hg⟩ => by
  simp [hf, hg, to_inj] at h
  rw [← h]
  exact rel.trans (rel.coprod_mk_congr (to_inj_eq_inl hf) (to_inj_eq_inl hg))
    (rel.comp_inl_coprod_mk _ _).symm

theorem to_inj_eq_inr : {X Y Z : prod_coprod C} → {f : norm_hom X (coprod Y Z)} →
  {g : norm_hom X Z} → to_inj f = some (Sum.inr g) → rel f g.comp_inr
| _, _, _, comp_inr f, g, h => by
  simp [to_inj] at h
  simp [h]
  exact rel.refl _
  | _, _, _, comp_inl f, g, h => by
  simp [to_inj] at h
| _, _, _, snd_comp f, g, h =>
  have hi : ∃ i, to_inj f = some (Sum.inr i) := by
  { simp [to_inj] at h
    revert h
    match to_inj f with
    | some (Sum.inr i) => intro h; exact ⟨i, rfl⟩
    | some (Sum.inl _) => simp
    | none => simp }
  match hi with
  | ⟨i, hi⟩ => by
  simp [hi, to_inj] at h
  rw [← h]
  exact rel.trans (rel.snd_comp_congr (to_inj_eq_inr hi))
    (rel.snd_comp_comp_inr i).symm
| _, _, _, fst_comp f, g, h =>
  have hi : ∃ i, to_inj f = some (Sum.inr i) := by
  { simp [to_inj] at h
    revert h
    match to_inj f with
    | some (Sum.inr i) => intro h; exact ⟨i, rfl⟩
    | some (Sum.inl _) => simp
    | none => simp }
  match hi with
  | ⟨i, hi⟩ => by
  simp [hi, to_inj] at h
  rw [← h]
  exact rel.trans (rel.fst_comp_congr (to_inj_eq_inr hi))
    (rel.fst_comp_comp_inr i).symm
| _, _, _, coprod_mk f g, i, h =>
  have hi : ∃ f' g', to_inj f = some (Sum.inr f') ∧ to_inj g = some (Sum.inr g') := by
  { simp [to_inj] at h
    revert h
    match to_inj f, to_inj g with
    | some (Sum.inr f'), some (Sum.inr g') => intro _; exact ⟨f', g', rfl, rfl⟩
    | some (Sum.inl _), some (Sum.inl _) => simp
    | none, _ => simp
    | _, none => simp
    | some (Sum.inr _), some (Sum.inl _) => simp
    | some (Sum.inl _), some (Sum.inr _) => simp }
  match hi with
  | ⟨f', g', hf, hg⟩ => by
  simp [hf, hg, to_inj] at h
  rw [← h]
  exact rel.trans (rel.coprod_mk_congr (to_inj_eq_inr hf) (to_inj_eq_inr hg))
    (rel.comp_inr_coprod_mk _ _).symm

theorem to_inj_eq_none {X Y Z : prod_coprod C} {f : norm_hom X (coprod Y Z)}
  (hf : to_inj f = none) {g : norm_hom X Z} : ¬rel f g.comp_inr := by
intro h
cases h
simp at hf


end norm_hom