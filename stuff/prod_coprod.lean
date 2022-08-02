
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

inductive list_proj : (X Y : prod_coprod C) → Type -- Y is not prod
| empty {X : prod_coprod C} : list_proj X X
| fst_comp {X Y Z : prod_coprod C} (f : list_proj X Z) : list_proj (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : list_proj Y Z) : list_proj (prod X Y) Z

inductive list_inj : (X Y : prod_coprod C) → Type -- X is not coprod
| empty {X : prod_coprod C} : list_inj X X
| comp_inl {X Y Z : prod_coprod C} (f : list_inj X Y) : list_inj X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : list_inj X Z) : list_inj X (coprod Y Z)

inductive norm_hom : prod_coprod C → prod_coprod C → Type
| prod_mk_of_cat {W : C} {X Y Z : prod_coprod C}
  (f : norm_hom (of_cat' W) X) (g : norm_hom (of_cat' W) Y)
  (h : list_inj (prod X Y) Z) :
  norm_hom (of_cat' W) Z
| prod_mk_prod {V W X Y Z : prod_coprod C}
  (f : norm_hom (prod V W) X) (g : norm_hom (prod V W) Y)
  (h : list_inj (prod X Y) Z) :
  norm_hom (prod V W) Z
| coprod_mk_of_cat {W X Y : prod_coprod C} {Z : C}
  (f : list_proj W (coprod X Y))
  (g : norm_hom X (of_cat' Z)) (h : norm_hom Y (of_cat' Z)) :
  norm_hom W (of_cat' Z)
| coprod_mk_coprod {V W X Y Z : prod_coprod C}
  (f : list_proj V (coprod W X))
  (g : norm_hom W (coprod Y Z)) (h : norm_hom X (coprod Y Z)) :
  norm_hom V (coprod Y Z)
| prod_mk_coprod {W X Y Z : prod_coprod C}
  (f : norm_hom (coprod W X) Y) (g : norm_hom (coprod W X) Z) :
  norm_hom (coprod W X) (prod Y Z)
| of_cat {W : prod_coprod C} {X Y : C} {Z : prod_coprod C}
  (f : list_proj W (of_cat' X)) (g : X ⟶ Y)
  (h : list_inj (of_cat' Y) Z) : norm_hom W Z

namespace norm_hom

open list_inj list_proj

def prod_mk : {X Y Z : prod_coprod C} → (f : norm_hom X Y) → (g : norm_hom X Z) →
  norm_hom X (prod Y Z)
| (of_cat' _), _, _, f, g => prod_mk_of_cat f g empty
| (coprod _ _), _, _, f, g => prod_mk_coprod f g
| (prod _ _), _ ,_, f, g => prod_mk_prod f g empty

def comp_fst : {X Y Z : prod_coprod C} → (f : norm_hom X (prod Y Z)) → norm_hom X Y
| _, _, _, (prod_mk_of_cat f g list_inj.empty) => f
| _, _, _, (prod_mk_prod f g list_inj.empty) => f
| _, _, _, (prod_mk_coprod f g) => f

@[simp] theorem comp_fst_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  comp_fst (prod_mk f g) = f :=
by cases X <;> simp [comp_fst, prod_mk]

def comp_snd : {X Y Z : prod_coprod C} → (f : norm_hom X (prod Y Z)) → norm_hom X Z
| _, _, _, (prod_mk_of_cat f g list_inj.empty) => g
| _, _, _, (prod_mk_prod f g list_inj.empty) => g
| _, _, _, (prod_mk_coprod f g) => g

@[simp] theorem comp_snd_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  comp_snd (prod_mk f g) = g :=
by cases X <;> simp [comp_snd, prod_mk]

theorem prod_eta : {X Y Z : prod_coprod C} → (f : norm_hom X (prod Y Z)) →
  prod_mk (comp_fst f) (comp_snd f) = f
| _, _, _, (prod_mk_of_cat f g list_inj.empty) => rfl
| _, _, _, (prod_mk_prod f g list_inj.empty) => rfl
| _, _, _, (prod_mk_coprod f g) => rfl

def coprod_mk : {X Y Z : prod_coprod C} → (f : norm_hom X Z) → (g : norm_hom Y Z) →
  norm_hom (coprod X Y) Z
| _, _, (of_cat' _), f, g => coprod_mk_of_cat empty f g
| _, _, (coprod _ _), f, g => coprod_mk_coprod empty f g
| _, _, (prod _ _), f, g => prod_mk_coprod
  (coprod_mk (comp_fst f) (comp_fst g))
  (coprod_mk (comp_snd f) (comp_snd g))

theorem coprod_mk_comp_fst {W X Y Z : prod_coprod C}
  (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)) :
  comp_fst (coprod_mk f g) = coprod_mk (comp_fst f) (comp_fst g) :=
by
  cases Y <;>
  simp [coprod_mk, comp_fst]

theorem coprod_mk_comp_snd {W X Y Z : prod_coprod C}
  (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)) :
  comp_snd (coprod_mk f g) = coprod_mk (comp_snd f) (comp_snd g) :=
by
  intros
  cases Y <;>
  simp [coprod_mk, comp_snd]

def inl_comp : {X Y Z : prod_coprod C} → norm_hom (coprod X Y) Z → norm_hom X Z
| _, _, _, (coprod_mk_of_cat list_proj.empty g h) => g
| _, _, _, (coprod_mk_coprod list_proj.empty g h) => g
| _, _, _, prod_mk_coprod f g => prod_mk (inl_comp f) (inl_comp g)

def inr_comp : {X Y Z : prod_coprod C} → norm_hom (coprod X Y) Z → norm_hom Y Z
| _, _, _, (coprod_mk_of_cat list_proj.empty g h) => h
| _, _, _, (coprod_mk_coprod list_proj.empty g h) => h
| _, _, _, (prod_mk_coprod f g) => prod_mk (inr_comp f) (inr_comp g)

theorem inl_comp_comp_fst : {W X Y Z : prod_coprod C} → (f : norm_hom (coprod W X) (prod Y Z)) →
  inl_comp (comp_fst f) = comp_fst (inl_comp f)
| _, _, _, _, (prod_mk_coprod f g) => by
rw [inl_comp, comp_fst]
simp

theorem inr_comp_comp_fst : {W X Y Z : prod_coprod C} → (f : norm_hom (coprod W X) (prod Y Z)) →
  inr_comp (comp_fst f) = comp_fst (inr_comp f)
| _, _, _, _, (prod_mk_coprod f g) => by
rw [comp_fst, inr_comp]
simp

theorem inl_comp_comp_snd : {W X Y Z : prod_coprod C} → (f : norm_hom (coprod W X) (prod Y Z)) →
  inl_comp (comp_snd f) = comp_snd (inl_comp f)
| A, B, D, _, (prod_mk_coprod f g) => by
rw [comp_snd, inl_comp]
simp

theorem inr_comp_comp_snd : {W X Y Z : prod_coprod C} → (f : norm_hom (coprod W X) (prod Y Z)) →
  inr_comp (comp_snd f) = comp_snd (inr_comp f)
| _, _, _, _, (prod_mk_coprod f g) => by
rw [comp_snd, inr_comp]
simp

@[simp] theorem inl_comp_coprod_mk : {X Y Z : prod_coprod C} → (f : norm_hom X Z) → (g : norm_hom Y Z) →
  inl_comp (coprod_mk f g) = f
| _, _, (of_cat' Z), _, _ => rfl
| _, _, (coprod Y Z), _, _ => rfl
| _, _, (prod Y Z), f, g =>
by rw [coprod_mk, inl_comp, inl_comp_coprod_mk, inl_comp_coprod_mk, prod_eta]

@[simp] theorem inr_comp_coprod_mk : {X Y Z : prod_coprod C} → (f : norm_hom X Z) → (g : norm_hom Y Z) →
  inr_comp (coprod_mk f g) = g
| _, _, (of_cat' Z), _, _ => rfl
| _, _, (coprod Y Z), _, _ => rfl
| _, _, (prod Y Z), f, g =>
by rw [coprod_mk, inr_comp, inr_comp_coprod_mk, inr_comp_coprod_mk, prod_eta]

theorem coprod_eta : {X Y Z : prod_coprod C} → (f : norm_hom (coprod X Y) Z) →
  coprod_mk (inl_comp f) (inr_comp f) = f
| _, _, _, (coprod_mk_of_cat list_proj.empty g h) => rfl
| _, _, _, (coprod_mk_coprod list_proj.empty g h) => rfl
| _, _, _, (prod_mk_coprod f g) =>
  by simp [coprod_mk, inl_comp, inr_comp, coprod_eta f, coprod_eta g]

def prod_mk_l : {W X Y Z : prod_coprod C} → (f : norm_hom W X) → (g : norm_hom W Y) →
  (h : list_inj (prod X Y) Z) → norm_hom W Z
| (of_cat' _), _, _, _, f, g, h => prod_mk_of_cat f g h
| (coprod V W), X, Y, Z, f, g, h =>
  coprod_mk
    (prod_mk_l (inl_comp f) (inl_comp g) h)
    (prod_mk_l (inr_comp f) (inr_comp g) h)
| (prod _ _), _, _, _, f, g, h => prod_mk_prod f g h

def coprod_mk_l : {W X Y Z : prod_coprod C} → (f : list_proj W (coprod X Y)) →
  (g : norm_hom X Z) → (h : norm_hom Y Z) → norm_hom W Z
| _, _, _, (of_cat' _), f, g, h => coprod_mk_of_cat f g h
| X, Y, Z, (prod V W), f, g, h =>
  prod_mk
    (coprod_mk_l f (comp_fst g) (comp_fst h))
    (coprod_mk_l f (comp_snd g) (comp_snd h))
| _, _, _, (coprod _ _), f, g, h => coprod_mk_coprod f g h

def fst_comp : {X Y Z : prod_coprod C} →
  (f : norm_hom X Z) → norm_hom (prod X Y) Z
| _, _, _, (prod_mk_of_cat f g h) =>
  prod_mk_l (fst_comp f) (fst_comp g) h
| _, _, _, (prod_mk_prod f g h) =>
  prod_mk_l (fst_comp f) (fst_comp g) h
| _, _, _, (prod_mk_coprod f g) =>
  prod_mk (fst_comp f) (fst_comp g)
| _, _, _, (coprod_mk_of_cat f g h) => coprod_mk_of_cat f.fst_comp g h
| _, _, _, (coprod_mk_coprod f g h) => coprod_mk_coprod f.fst_comp g h
| _, _, _, (of_cat f g h) => of_cat f.fst_comp g h

def snd_comp : {X Y Z : prod_coprod C} →
  (f : norm_hom Y Z) → norm_hom (prod X Y) Z
| _, _, _, (prod_mk_of_cat f g h) =>
  prod_mk_l (snd_comp f) (snd_comp g) h
| _, _, _, (prod_mk_prod f g h) =>
  prod_mk_l (snd_comp f) (snd_comp g) h
| _, _, _, (prod_mk_coprod f g) =>
  prod_mk (snd_comp f) (snd_comp g)
| _, _, _, (coprod_mk_of_cat f g h) => coprod_mk_of_cat f.snd_comp g h
| _, _, _, (coprod_mk_coprod f g h) => coprod_mk_coprod f.snd_comp g h
| _, _, _, (of_cat f g h) => of_cat f.snd_comp g h

@[simp] def list_proj_comp : {X Y Z : prod_coprod C} → (f : list_proj X Y) →
  (g : norm_hom Y Z) → norm_hom X Z
| _, _, _, list_proj.empty, g => g
| _, _, _, list_proj.fst_comp f, g => fst_comp (list_proj_comp f g)
| _, _, _, list_proj.snd_comp f, g => snd_comp (list_proj_comp f g)

@[simp] theorem list_proj_comp_coprod_mk_of_cat : {W X Y : prod_coprod C} → {Z : C} →
  (f : list_proj W (coprod X Y)) →
  (g : norm_hom X (of_cat' Z)) → (h : norm_hom Y (of_cat' Z)) →
  list_proj_comp f (coprod_mk_of_cat empty g h) = coprod_mk_of_cat f g h
| _, _, _, _, list_proj.empty, _, _ => rfl
| _, _, _, _, (list_proj.fst_comp f), g, h =>
by rw [list_proj_comp, list_proj_comp_coprod_mk_of_cat, fst_comp]
| _, _, _, _, (list_proj.snd_comp f), g, h =>
by rw [list_proj_comp, list_proj_comp_coprod_mk_of_cat, snd_comp]

@[simp] theorem list_proj_comp_coprod_mk_coprod : {V W X Y Z : prod_coprod C} →
  (f : list_proj V (coprod W X)) →
  (g : norm_hom W (coprod Y Z)) → (h : norm_hom X (coprod Y Z)) →
  list_proj_comp f (coprod_mk_coprod empty g h) = coprod_mk_coprod f g h
| _, _, _, _, _, list_proj.empty, _, _ => rfl
| _, _, _, _, _, (list_proj.fst_comp f), g, h =>
by rw [list_proj_comp, list_proj_comp_coprod_mk_coprod, fst_comp]
| _, _, _, _, _, (list_proj.snd_comp f), g, h =>
by rw [list_proj_comp, list_proj_comp_coprod_mk_coprod, snd_comp]

@[simp] theorem list_proj_comp_of_cat : {W : prod_coprod C} → {X Y : C} → {Z : prod_coprod C} →
  (f : list_proj W (of_cat' X)) → (g : X ⟶ Y) →
  (h : list_inj (of_cat' Y) Z) →
  list_proj_comp f (of_cat empty g h) = of_cat f g h
| _, _, _, _, list_proj.empty, _, _ => rfl
| _, _, _, _, (list_proj.fst_comp f), g, h =>
by rw [list_proj_comp, list_proj_comp_of_cat, fst_comp]
| _, _, _, _, (list_proj.snd_comp f), g, h =>
by rw [list_proj_comp, list_proj_comp_of_cat, snd_comp]

def comp_inl : {X Y Z : prod_coprod C} →
  (f : norm_hom X Y) → norm_hom X (coprod Y Z)
| _, _, _, (coprod_mk_of_cat f g h) =>
  coprod_mk_l f (comp_inl g) (comp_inl h)
| _, _, _, (coprod_mk_coprod f g h) =>
  coprod_mk_l f (comp_inl g) (comp_inl h)
| _, _, _, (prod_mk_of_cat f g h) => prod_mk_of_cat f g h.comp_inl
| _, _, _, (prod_mk_prod f g h) => prod_mk_prod f g h.comp_inl
| _, _, _, (prod_mk_coprod f g) =>
  prod_mk_l f g list_inj.empty.comp_inl
| _, _, _, (of_cat f g h) => of_cat f g h.comp_inl

def comp_inr : {X Y Z : prod_coprod C} →
  (f : norm_hom X Z) → norm_hom X (coprod Y Z)
| _, _, _, (coprod_mk_of_cat f g h) =>
  coprod_mk_l f (comp_inr g) (comp_inr h)
| _, _, _, (coprod_mk_coprod f g h) =>
  coprod_mk_l f (comp_inr g) (comp_inr h)
| _, _, _, (prod_mk_of_cat f g h) => prod_mk_of_cat f g h.comp_inr
| _, _, _, (prod_mk_prod f g h) => prod_mk_prod f g h.comp_inr
| _, _, _, (prod_mk_coprod f g) =>
  prod_mk_l f g list_inj.empty.comp_inr
| _, _, _, (of_cat f g h) => of_cat f g h.comp_inr

protected def id : (X : prod_coprod C) → norm_hom X X
| (of_cat' X) => of_cat empty (𝟙 X) empty
| (prod X Y) => prod_mk (fst_comp (norm_hom.id X)) (snd_comp (norm_hom.id Y))
| (coprod X Y) => coprod_mk (comp_inl (norm_hom.id X)) (comp_inr (norm_hom.id Y))

@[simp] def comp_list_inj : {X Y Z : prod_coprod C} → (f : norm_hom X Y) → (g : list_inj Y Z) →
  norm_hom X Z
| _, _, _, f, list_inj.empty => f
| _, _, _, f, list_inj.comp_inl g => comp_inl (comp_list_inj f g)
| _, _, _, f, list_inj.comp_inr g => comp_inr (comp_list_inj f g)

@[simp] theorem comp_list_inj_prod_mk_of_cat : {W : C} → {X Y Z : prod_coprod C} →
  (f : norm_hom (of_cat' W) X) → (g : norm_hom (of_cat' W) Y) →
  (h : list_inj (prod X Y) Z) → comp_list_inj (prod_mk_of_cat f g empty) h = prod_mk_of_cat f g h
| _, _, _, _, _, _, list_inj.empty => by simp [comp_list_inj]
| _, _, _, _, _, _, (list_inj.comp_inl h) =>
by rw [comp_list_inj, comp_list_inj_prod_mk_of_cat, comp_inl]
| _, _, _, _, _, _, (list_inj.comp_inr h) =>
by rw [comp_list_inj, comp_list_inj_prod_mk_of_cat, comp_inr]

@[simp] theorem comp_list_inj_prod_mk_prod : {V W X Y Z : prod_coprod C} →
  (f : norm_hom (prod V W) X) → (g : norm_hom (prod V W) Y) →
  (h : list_inj (prod X Y) Z) →
  comp_list_inj (prod_mk_prod f g empty) h = prod_mk_prod f g h
| _, _, _, _, _, _, _, list_inj.empty => by simp
| _, _, _, _, _, _, _, (list_inj.comp_inl h) =>
by rw [comp_list_inj, comp_list_inj_prod_mk_prod, comp_inl]
| _, _, _, _, _, _, _, (list_inj.comp_inr h) =>
by rw [comp_list_inj, comp_list_inj_prod_mk_prod, comp_inr]

@[simp] theorem comp_list_inj_of_cat : {W : prod_coprod C} → {X Y : C} → {Z : prod_coprod C} →
  (f : list_proj W (of_cat' X)) → (g : X ⟶ Y) →
  (h : list_inj (of_cat' Y) Z) →
  comp_list_inj (of_cat f g empty) h = of_cat f g h
| _, _, _, _, _, _, list_inj.empty => rfl
| _, _, _, _, _, _, (list_inj.comp_inl h) =>
by rw [comp_list_inj, comp_list_inj_of_cat, comp_inl]
| _, _, _, _, _, _, (list_inj.comp_inr h) =>
by rw [comp_list_inj, comp_list_inj_of_cat, comp_inr]

def get_proj_of_cat : {X Y : prod_coprod C} → {Z : C} →
  (f : norm_hom (prod X Y) (of_cat' Z)) →
  norm_hom X (of_cat' Z) ⊕ norm_hom Y (of_cat' Z)
| _, _, _, (coprod_mk_of_cat (list_proj.fst_comp f) g h) =>
  Sum.inl (coprod_mk_of_cat f g h)
| _, _, _, (coprod_mk_of_cat (list_proj.snd_comp f) g h) =>
  Sum.inr (coprod_mk_of_cat f g h)
| _, _, _, (of_cat (list_proj.fst_comp f) g h) =>
  Sum.inl (of_cat f g h)
| _, _, _, (of_cat (list_proj.snd_comp f) g h) =>
  Sum.inr (of_cat f g h)

def get_inj_of_cat : {X : C} → {Y Z : prod_coprod C} →
  (f : norm_hom (of_cat' X) (coprod Y Z)) →
  norm_hom (of_cat' X) Y ⊕ norm_hom (of_cat' X) Z
| _, _, _, (prod_mk_of_cat f g (list_inj.comp_inl h)) =>
  Sum.inl (prod_mk_of_cat f g h)
| _, _, _, (prod_mk_of_cat f g (list_inj.comp_inr h)) =>
  Sum.inr (prod_mk_of_cat f g h)
| _, _, _, (of_cat f g (list_inj.comp_inl h)) =>
  Sum.inl (of_cat f g h)
| _, _, _, (of_cat f g (list_inj.comp_inr h)) =>
  Sum.inr (of_cat f g h)

end norm_hom

inductive norm_hom2 : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} (f : X ⟶ Y) : norm_hom2 (of_cat' X) (of_cat' Y)
| coprod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Z) (g : norm_hom2 Y Z) :
  norm_hom2 (X.coprod Y) Z
| comp_inl {X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2 X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : norm_hom2 X Z) :
  norm_hom2 X (coprod Y Z)
| prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
  norm_hom2 X (prod Y Z)
| fst_comp {X Y Z : prod_coprod C} (f : norm_hom2 X Z) :
  norm_hom2 (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : norm_hom2 Y Z) :
  norm_hom2 (prod X Y) Z

namespace norm_hom2

@[simp] def list_proj_comp : {X Y Z : prod_coprod C} → (f : list_proj X Y) →
  (g : norm_hom2 Y Z) → norm_hom2 X Z
| _, _, _, list_proj.empty, g => g
| _, _, _, list_proj.fst_comp f, g => fst_comp (list_proj_comp f g)
| _, _, _, list_proj.snd_comp f, g => snd_comp (list_proj_comp f g)

@[simp] def comp_list_inj : {X Y Z : prod_coprod C} → (f : norm_hom2 X Y) → (g : list_inj Y Z) →
  norm_hom2 X Z
| _, _, _, f, list_inj.empty => f
| _, _, _, f, list_inj.comp_inl g => comp_inl (comp_list_inj f g)
| _, _, _, f, list_inj.comp_inr g => comp_inr (comp_list_inj f g)

end norm_hom2

@[simp] def norm_hom.to_norm_hom2 : {X Y : prod_coprod C} → (f : norm_hom X Y) → norm_hom2 X Y
| _, _, (norm_hom.of_cat f g h) => (norm_hom2.list_proj_comp f (norm_hom2.of_cat g)).comp_list_inj h
| _, _, (norm_hom.prod_mk_of_cat f g h) =>
  norm_hom2.comp_list_inj (norm_hom2.prod_mk (to_norm_hom2 f) (to_norm_hom2 g)) h
| _, _, (norm_hom.prod_mk_prod f g h) =>
  norm_hom2.comp_list_inj (norm_hom2.prod_mk (to_norm_hom2 f) (to_norm_hom2 g)) h
| _, _, (norm_hom.prod_mk_coprod f g) =>
  norm_hom2.prod_mk (to_norm_hom2 f) (to_norm_hom2 g)
| _, _, (norm_hom.coprod_mk_of_cat f g h) =>
  norm_hom2.list_proj_comp f (norm_hom2.coprod_mk (to_norm_hom2 g) (to_norm_hom2 h))
| _, _, (norm_hom.coprod_mk_coprod f g h) =>
  norm_hom2.list_proj_comp f (norm_hom2.coprod_mk (to_norm_hom2 g) (to_norm_hom2 h))

@[simp] def norm_hom2.to_norm_hom : {X Y : prod_coprod C} → (f : norm_hom2 X Y) → norm_hom X Y
| _, _, (norm_hom2.of_cat f) => norm_hom.of_cat list_proj.empty f list_inj.empty
| _, _, (norm_hom2.comp_inl f) => norm_hom.comp_inl (to_norm_hom f)
| _, _, (norm_hom2.comp_inr f) => norm_hom.comp_inr (to_norm_hom f)
| _, _, (norm_hom2.fst_comp f) => norm_hom.fst_comp (to_norm_hom f)
| _, _, (norm_hom2.snd_comp f) => norm_hom.snd_comp (to_norm_hom f)
| _, _, (norm_hom2.prod_mk f g) => norm_hom.prod_mk (to_norm_hom f) (to_norm_hom g)
| _, _, (norm_hom2.coprod_mk f g) => norm_hom.coprod_mk (to_norm_hom f) (to_norm_hom g)

@[simp] theorem to_norm_hom_list_proj_comp {X Y Z : prod_coprod C} (f : list_proj X Y) (g : norm_hom2 Y Z) :
  (norm_hom2.list_proj_comp f g).to_norm_hom = g.to_norm_hom.list_proj_comp f :=
by induction f <;> simp [*]

@[simp] theorem to_norm_hom_comp_list_inj {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : list_inj Y Z) :
  (norm_hom2.comp_list_inj f g).to_norm_hom = f.to_norm_hom.comp_list_inj g :=
by induction g <;> simp [*]

def norm_hom2.size : {X Y : prod_coprod C} → norm_hom2 X Y → Nat
| _, _, (norm_hom2.of_cat f) => 0
| _, _, (norm_hom2.comp_inl f) => size f + 1
| _, _, (norm_hom2.comp_inr f) => size f + 1
| _, _, (norm_hom2.fst_comp f) => size f + 1
| _, _, (norm_hom2.snd_comp f) => size f + 1
| _, _, (norm_hom2.prod_mk f g) => size f + size g + 1
| _, _, (norm_hom2.coprod_mk f g) => size f + size g + 1

def norm_hom2.comp : {X Y Z : prod_coprod C} → (f : norm_hom2 X Y) →
  (g : norm_hom2 Y Z) → norm_hom2 X Z
| _, _, _, norm_hom2.coprod_mk f g, h =>
  have wf₁ : size f + 0 < size (coprod_mk f g) := by
    rw [size, Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.succ_pos _) _
  have wf₂ : size g < size (coprod_mk f g) := by
    rw [size, Nat.add_comm (size f), Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.succ_pos _) _
  norm_hom2.coprod_mk (comp f h) (comp g h)
| _, _, _, norm_hom2.fst_comp f, g =>
  norm_hom2.fst_comp (comp f g)
| _, _, _, norm_hom2.snd_comp f, g =>
  norm_hom2.snd_comp (comp f g)
| _, _, _, f, norm_hom2.prod_mk g h =>
  have wf₁ : size g + 0 < size (prod_mk g h) := by
    rw [size, Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.succ_pos _) _
  have wf₂ : size h < size (prod_mk g h) := by
    rw [size, Nat.add_comm (size g), Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.succ_pos _) _
  norm_hom2.prod_mk (comp f g) (comp f h)
| _, _, _, f, (comp_inl g) => comp_inl (comp f g)
| _, _, _, f, (comp_inr g) => comp_inr (comp f g)
| _, _, _, norm_hom2.of_cat f, norm_hom2.of_cat g =>
  norm_hom2.of_cat (f ≫ g)
| _, _, _, comp_inl f, norm_hom2.coprod_mk g h => comp f g
| _, _, _, comp_inr f, norm_hom2.coprod_mk g h => comp f h
| _, _, _, norm_hom2.prod_mk f g, norm_hom2.fst_comp h =>
  have wf₁ : size f + 0 < size (prod_mk f g) := by
    rw [size, Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.succ_pos _) _
  comp f h
| _, _, _, norm_hom2.prod_mk f g, norm_hom2.snd_comp h =>
  have wf₂ : size g < size (prod_mk f g) := by
    rw [size, Nat.add_comm (size f), Nat.add_assoc]
    exact Nat.add_lt_add_left (Nat.succ_pos _) _
  comp g h
termination_by comp f g => (size f, size g)

theorem to_norm_hom_to_norm_hom2 {X Y : prod_coprod C} (f : norm_hom X Y) :
  f.to_norm_hom2.to_norm_hom = f :=
by induction f <;> simp [norm_hom.to_norm_hom2, norm_hom2.to_norm_hom, *,
   norm_hom.prod_mk, norm_hom.coprod_mk]

theorem norm_hom2.comp_assoc : {W X Y Z : prod_coprod C} →
  (f : norm_hom2 W X) → (g : norm_hom2 X Y) → (h : norm_hom2 Y Z) →
  ((f.comp g).comp h).to_norm_hom =
    (f.comp (g.comp h)).to_norm_hom
| _, _, _, _, fst_comp f, g, h => by
  rw [norm_hom2.comp]

-- induction f <;>
-- induction g <;>
-- cases hX <;>
-- induction h <;>
-- cases hY <;>
-- --simp at [*]


-- def comp_fst : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)), norm_hom X Y
-- | _ _ _ (@prod_mk_of_cat _ _ W X Y Z f g empty) := f
-- | A B D (@prod_mk_prod _ _ V W X Y Z f g empty) := f
-- | A B D (@prod_mk_coprod _ _ W X Y Z f g) := f

-- @[simp] theorem comp_fst_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
--   comp_fst (prod_mk f g) = f :=
-- by cases X; simp [comp_fst, prod_mk]

-- def comp_snd : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)), norm_hom X Z
-- | _ _ _ (@prod_mk_of_cat _ _ W X Y Z f g empty) := g
-- | A B D (@prod_mk_prod _ _ V W X Y Z f g empty) := g
-- | A B D (@prod_mk_coprod _ _ W X Y Z f g) := g

-- @[simp] theorem comp_snd_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
--   comp_snd (prod_mk f g) = g :=
-- by cases X; simp [comp_snd, prod_mk]

-- theorem prod_eta : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)),
--   prod_mk (comp_fst f) (comp_snd f) = f
-- | _ _ _ (prod_mk_of_cat f g empty) := rfl
-- | _ _ _ (prod_mk_prod f g empty) := rfl
-- | _ _ _ (prod_mk_coprod f g) := rfl

-- def coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
--   norm_hom (coprod X Y) Z
-- | _ _ (of_cat' _) f g := coprod_mk_of_cat empty f g
-- | _ _ (coprod _ _) f g := coprod_mk_coprod empty f g
-- | _ _ (prod _ _) f g := prod_mk_coprod
--   (coprod_mk (comp_fst f) (comp_fst g))
--   (coprod_mk (comp_snd f) (comp_snd g))

-- theorem coprod_mk_comp_fst : Π {W X Y Z : prod_coprod C}
--   (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)),
--   comp_fst (coprod_mk f g) = coprod_mk (comp_fst f) (comp_fst g) :=
-- begin
--   intros,
--   cases Y;
--   dsimp [coprod_mk, comp_fst]; refl
-- end

-- theorem coprod_mk_comp_snd : Π {W X Y Z : prod_coprod C}
--   (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)),
--   comp_snd (coprod_mk f g) = coprod_mk (comp_snd f) (comp_snd g) :=
-- begin
--   intros,
--   cases Y;
--   dsimp [coprod_mk, comp_fst]; refl
-- end

-- def inl_comp : Π {X Y Z : prod_coprod C}, norm_hom (coprod X Y) Z → norm_hom X Z
-- | _ _ _ (coprod_mk_of_cat empty g h) := g
-- | _ _ _ (coprod_mk_coprod empty g h) := g
-- | _ _ _ (@prod_mk_coprod _ _ W X Y Z f g) := prod_mk (inl_comp f) (inl_comp g)

-- def inr_comp : Π {X Y Z : prod_coprod C}, norm_hom (coprod X Y) Z → norm_hom Y Z
-- | _ _ _ (coprod_mk_of_cat empty g h) := h
-- | _ _ _ (coprod_mk_coprod empty g h) := h
-- | _ _ _ (@prod_mk_coprod _ _ W X Y Z f g) := prod_mk (inr_comp f) (inr_comp g)

-- theorem inl_comp_comp_fst : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inl_comp (comp_fst f) = comp_fst (inl_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_fst, inl_comp]

-- theorem inr_comp_comp_fst : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inr_comp (comp_fst f) = comp_fst (inr_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_fst, inr_comp]

-- theorem inl_comp_comp_snd : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inl_comp (comp_snd f) = comp_snd (inl_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_snd, inl_comp]

-- theorem inr_comp_comp_snd : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inr_comp (comp_snd f) = comp_snd (inr_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_snd, inr_comp]

-- @[simp] theorem inl_comp_coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
--   inl_comp (coprod_mk f g) = f
-- | _ _ (of_cat' Z) _ _ := rfl
-- | _ _ (coprod Y Z) _ _ := rfl
-- | _ _ (prod Y Z) f g :=
-- by rw [coprod_mk, inl_comp, inl_comp_coprod_mk, inl_comp_coprod_mk, prod_eta]

-- @[simp] theorem inr_comp_coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
--   inr_comp (coprod_mk f g) = g
-- | _ _ (of_cat' Z) _ _ := rfl
-- | _ _ (coprod Y Z) _ _ := rfl
-- | _ _ (prod Y Z) f g :=
-- by rw [coprod_mk, inr_comp, inr_comp_coprod_mk, inr_comp_coprod_mk, prod_eta]

-- theorem coprod_eta : Π {X Y Z : prod_coprod C} (f : norm_hom (coprod X Y) Z),
--   coprod_mk (inl_comp f) (inr_comp f) = f
-- | _ _ _ (coprod_mk_of_cat empty g h) := rfl
-- | _ _ _ (coprod_mk_coprod empty g h) := rfl
-- | _ _ _ (prod_mk_coprod f g) :=
--   by simp [coprod_mk, inl_comp, inr_comp, coprod_eta f, coprod_eta g]

-- def prod_mk_l : Π {W X Y Z : prod_coprod C} (f : norm_hom W X) (g : norm_hom W Y)
--   (h : list_inj (prod X Y) Z), norm_hom W Z
-- | (of_cat' _) _ _ _ f g h := prod_mk_of_cat f g h
-- | (coprod V W) X Y Z f g h :=
--   coprod_mk
--     (prod_mk_l (inl_comp f) (inl_comp g) h)
--     (prod_mk_l (inr_comp f) (inr_comp g) h)
-- | (prod _ _) _ _ _ f g h := prod_mk_prod f g h

-- def coprod_mk_l : Π {W X Y Z : prod_coprod C} (f : list_proj W (coprod X Y))
--   (g : norm_hom X Z) (h : norm_hom Y Z), norm_hom W Z
-- | _ _ _ (of_cat' _) f g h := coprod_mk_of_cat f g h
-- | X Y Z (prod V W) f g h :=
--   prod_mk
--     (coprod_mk_l f (comp_fst g) (comp_fst h))
--     (coprod_mk_l f (comp_snd g) (comp_snd h))
-- | _ _ _ (coprod _ _) f g h := coprod_mk_coprod f g h

-- def fst_comp : Π {X Y Z : prod_coprod C}
--   (f : norm_hom X Z), norm_hom (prod X Y) Z
-- | _ _ _ (prod_mk_of_cat f g h) :=
--   prod_mk_l (fst_comp f) (fst_comp g) h
-- | _ _ _ (prod_mk_prod f g h) :=
--   prod_mk_l (fst_comp f) (fst_comp g) h
-- | _ _ _ (prod_mk_coprod f g) :=
--   prod_mk (fst_comp f) (fst_comp g)
-- | _ _ _ (coprod_mk_of_cat f g h) := coprod_mk_of_cat f.fst_comp g h
-- | _ _ _ (coprod_mk_coprod f g h) := coprod_mk_coprod f.fst_comp g h
-- | _ _ _ (of_cat f g h) := of_cat f.fst_comp g h

-- def snd_comp : Π {X Y Z : prod_coprod C}
--   (f : norm_hom Y Z), norm_hom (prod X Y) Z
-- | _ _ _ (prod_mk_of_cat f g h) :=
--   prod_mk_l (snd_comp f) (snd_comp g) h
-- | _ _ _ (prod_mk_prod f g h) :=
--   prod_mk_l (snd_comp f) (snd_comp g) h
-- | _ _ _ (prod_mk_coprod f g) :=
--   prod_mk (snd_comp f) (snd_comp g)
-- | _ _ _ (coprod_mk_of_cat f g h) := coprod_mk_of_cat f.snd_comp g h
-- | _ _ _ (coprod_mk_coprod f g h) := coprod_mk_coprod f.snd_comp g h
-- | _ _ _ (of_cat f g h) := of_cat f.snd_comp g h

def comp {X Y Z : prod_coprod C} {b₁ b₂ : bool} (f : norm_hom b₁  X Y) (g : norm_hom b₂ Y Z) :
  Σ b : bool, norm_hom b X Z :=
norm_hom2.to_norm_hom (norm_hom2.comp (to_norm_hom2 f) g.to_norm_hom2)

@[simp] def norm_syn : Π {X Y : prod_coprod C} (f : syn X Y),
  Σ b : bool, norm_hom b X Y
| _ _ (syn.of_cat f) := ⟨ff, norm_hom.of_cat f⟩
| _ _ (syn.id _) := ⟨_, norm_hom.id _⟩
| _ _ (syn.comp f g) := (norm_syn f).2.comp (norm_syn g).2
| _ _ syn.fst := norm_hom.fst_comp (norm_hom.id _)
| _ _ syn.snd := norm_hom.snd_comp (norm_hom.id _)
| _ _ (syn.prod_mk f g) := ⟨ff, norm_hom.prod_mk (norm_syn f).2 (norm_syn g).2⟩
| _ _ syn.inl := norm_hom.comp_inl (norm_hom.id _)
| _ _ syn.inr := norm_hom.comp_inr (norm_hom.id _)
| _ _ (syn.coprod_mk f g) := ⟨ff, norm_hom.coprod_mk (norm_syn f).2 (norm_syn g).2⟩
#exit
@[simp] theorem to_hom_comp_inl : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y))),
  (@norm_hom.comp_inl _ _ _ _ Z f).to_norm_hom2.to_hom = f.to_norm_hom2.to_hom ≫ inl
| (of_cat' X) _ _ f := by simp [norm_hom.comp_inl]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) :=
  by ext; simp [norm_hom.comp_inl, to_hom_comp_inl f, to_hom_comp_inl g,
    ← category.assoc]
| (prod W X) Y Z (norm_hom.fst_comp f) := by simp [norm_hom.comp_inl, to_hom_comp_inl f]
| (prod W X) Y Z (norm_hom.snd_comp f) := by simp [norm_hom.comp_inl, to_hom_comp_inl f]
| (prod W X) Y Z (norm_hom.of_not_proj f) :=
  by simp [norm_hom.comp_inl, to_hom_comp_inl f.of_not_proj]

@[simp] theorem to_hom_comp_inr : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Z))),
  (@norm_hom.comp_inr _ _ X Y Z f).to_norm_hom2.to_hom = f.to_norm_hom2.to_hom ≫ inr
| (of_cat' X) _ _ f := by simp [norm_hom.comp_inr]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) :=
  by ext; simp [norm_hom.comp_inr, to_hom_comp_inr f, to_hom_comp_inr g,
    ← category.assoc]
| (prod W X) Y Z (norm_hom.fst_comp f) := by simp [norm_hom.comp_inr, to_hom_comp_inr f]
| (prod W X) Y Z (norm_hom.snd_comp f) := by simp [norm_hom.comp_inr, to_hom_comp_inr f]
| (prod W X) Y Z (norm_hom.of_not_proj f) :=
  by simp [norm_hom.comp_inr, to_hom_comp_inr f.of_not_proj]

@[simp] theorem to_hom_prod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y)))
  (g : norm_hom (sum.inl (X, Z))),
  (f.prod_mk g).to_norm_hom2.to_hom = prod_mk f.to_norm_hom2.to_hom g.to_norm_hom2.to_hom
| (of_cat' X) Y Z f g := by simp [norm_hom.prod_mk]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g.of_not_proj]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g.of_not_proj]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g.of_not_proj]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) (norm_hom.coprod_mk h i) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]

@[simp] theorem to_hom_comp : Π {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 Y Z),
  (f.comp g).to_hom = f.to_hom ≫ g.to_hom
| _ _ _ (norm_hom2.coprod_mk f g) h :=
  by ext; simp [to_hom_comp f, to_hom_comp g, ← category.assoc]
| _ _ _ (norm_hom2.fst_comp f) g :=
  by simp [to_hom_comp f]
| _ _ _ (norm_hom2.snd_comp f) g :=
  by simp [to_hom_comp f]
-- | _ _ _ f (norm_hom2.prod_mk g h) :=
-- | _ _ _ f (norm_hom2.comp_inl g) := g)
-- | _ _ _ f (norm_hom2.comp_inr g) :=
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.of_cat g) :=
  by simp
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.coprod_mk g h) :=
  by simp [to_hom_comp f]
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.coprod_mk g h) :=
  by simp [to_hom_comp f]
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.fst_comp h) :=
  by simp [to_hom_comp _ h, ← category.assoc]
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.snd_comp h) :=
  by simp [to_hom_comp _ h, ← category.assoc]
--repeated cases
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]



#exit
