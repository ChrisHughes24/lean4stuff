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
| of_cat : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod

variable {C}

namespace prod_coprod

@[simp] def size : prod_coprod C → Nat
| of_cat _ => 1
| prod X Y => size X + size Y + 1
| coprod X Y => size X + size Y + 1

inductive syn : (X Y : prod_coprod C) → Type
| map {X Y : C} : (X ⟶ Y) → syn (of_cat X) (of_cat Y)
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
| of_cat_id {X : C} : rel (syn.map (𝟙 X)) (syn.id (of_cat X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (syn.map (f ≫ g)) (syn.comp (syn.map f) (syn.map g))
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

inductive biprod (C : Type) [category C] : Type
| of_cat : C → biprod C
| sum : biprod C → biprod C → biprod C

namespace biprod

variable {C : Type} [category C]

@[simp] def size : biprod C → Nat
| of_cat _ => 1
| sum X Y => size X + size Y + 1

inductive hom : biprod C → biprod C → Type
| zero (X Y : C) : hom (of_cat X) (of_cat Y)
| scalar {X Y : C} : (X ⟶ Y) → hom (of_cat X) (of_cat Y)
| column {X : C} {Y Z : biprod C} : hom (of_cat X) Y → hom (of_cat X) Z →
  hom (of_cat X) (sum Y Z)
| row {X Y : biprod C} {Z : C} : hom X (of_cat Z) → hom Y (of_cat Z) →
  hom (sum X Y) (of_cat Z)
| matrix {W X Y Z : biprod C} : hom W Y → hom X Y → hom W Z → hom X Z →
  hom (sum W X) (sum Y Z)

open hom

def add : {X Y : biprod C} → hom X Y → hom X Y → hom X Y
| of_cat _, of_cat _, zero _ _, g => g
| of_cat _, of_cat _, scalar f, zero _ _ => scalar f
| of_cat _, of_cat _, scalar _, scalar _ => zero _ _
| of_cat _, sum _ _, column f g, column h i =>
  column (add f h) (add g i)
| sum _ _, of_cat _, row f g, row h i =>
  row (add f h) (add g i)
| sum _ _, sum _ _, matrix a₁ b₁ c₁ d₁, matrix a₂ b₂ c₂ d₂ =>
  matrix (add a₁ a₂) (add b₁ b₂) (add c₁ c₂) (add d₁ d₂)

def zero : {X Y : biprod C} → hom X Y
| of_cat _, of_cat _ => hom.zero _ _
| of_cat _, sum _ _ => column zero zero
| sum _ _, of_cat _ => row zero zero
| sum _ _, sum _ _ => matrix zero zero zero zero
termination_by zero X Y => (size X, size Y)

@[simp] theorem add_zero : {X Y : biprod C} → (f : hom X Y) →
  add f zero = f
| of_cat _, of_cat _, hom.zero _ _ => rfl
| of_cat _, of_cat _, scalar f => rfl
| of_cat _, sum _ _, column f g => by rw [zero, add, add_zero, add_zero]
| sum _ _, of_cat _, row f g => by rw [zero, add, add_zero, add_zero]
| sum _ _, sum _ _, matrix a₁ b₁ c₁ d₁ =>
  by rw [zero, add, add_zero, add_zero, add_zero, add_zero]
termination_by add_zero X Y f => (size X, size Y)

@[simp] theorem zero_add : {X Y : biprod C} → (f : hom X Y) →
  add zero f = f
| _, _, hom.zero _ _ => rfl
| _, _, scalar f => rfl
| _, _, column f g => by rw [zero, add, zero_add, zero_add]
| _, _, row f g => by rw [zero, add, zero_add, zero_add]
| _, _, matrix a₁ b₁ c₁ d₁ =>
  by rw [zero, add, zero_add, zero_add, zero_add, zero_add]
termination_by zero_add X Y f => (size X, size Y)

def prod_mk : {X Y Z : biprod C} → (f : hom X Y) → (g : hom X Z) → hom X (sum Y Z)
| of_cat _, _, _, f, g => column f g
| sum _ _, _, _, row a b, row c d => matrix a b c d
| sum _ _, _, _, matrix a b c d, row e f => matrix (prod_mk a c) (prod_mk b d) e f
| sum _ _, _, _, matrix a b c d, matrix e f g h =>
  matrix (prod_mk a c) (prod_mk b d) (prod_mk e g) (prod_mk f h)
| sum _ _, _, _, row a b, matrix c d e f => matrix a b (prod_mk c e) (prod_mk d f)

def coprod_mk : {X Y Z : biprod C} → (f : hom X Z) → (g : hom Y Z) → hom (sum X Y) Z
| _, _, of_cat _, f, g => row f g
| _, _, sum _ _, column a b, column c d => matrix a c b d
| _, _, sum _ _, column a b, matrix c d e f =>
  matrix a (coprod_mk c d) b (coprod_mk e f)
| _, _, sum _ _, matrix a b c d, matrix e f g h =>
  matrix (coprod_mk a b) (coprod_mk e f) (coprod_mk c d) (coprod_mk g h)
| _, _, sum _ _, matrix a b c d, column e f =>
  matrix (coprod_mk a b) e (coprod_mk c d) f

def comp {X Y Z : biprod C} : hom X Y → hom Y Z → hom X Z
| hom.zero _ _,  g => zero
| scalar f, hom.zero _ _ => zero
| scalar f, scalar g => scalar (f ≫ g)
| scalar f, column a b => column (comp (scalar f) a) (comp (scalar f) b)
| column a b, row c d => add (comp a c) (comp b d)
| column a b, matrix c d e f => column (add (comp a c) (comp b d))
  (add (comp a e) (comp b f))
| row a b, scalar c => row (comp a (scalar c)) (comp b (scalar c))
| row _ _, hom.zero _ _ => zero
| row a b, column c d => matrix (comp a c) (comp b c) (comp a d) (comp b d)
| matrix a b c d, row e f => row (add (comp a e) (comp c f))
  (add (comp b e) (comp d f))
| matrix a b c d, matrix e f g h =>
  matrix
    (add (comp a e) (comp c f))
    (add (comp b e) (comp d f))
    (add (comp a g) (comp c h))
    (add (comp b g) (comp d h))
termination_by comp X Y Z f g => (size X, size Y, size Z)

@[simp] theorem comp_zero : {X Y Z : biprod C} → (f : hom X Y) →
  comp f (@zero _ _ Y Z) = zero
| _, _, _, hom.zero _ _ => by rw [comp]
| _, _, of_cat _, matrix _ _ _ _ => by
  rw [zero, comp, zero, comp_zero, zero_add, comp_zero, comp_zero, zero_add, comp_zero]
| _, _, sum _ _, matrix _ _ _ _ => by
  rw [zero, comp, zero, comp_zero, zero_add, comp_zero, comp_zero, zero_add, comp_zero,
     comp_zero, zero_add, comp_zero, comp_zero, zero_add, comp_zero]
| _, _, of_cat _, row _ _ => by rw [zero, comp]
| _, _, sum _ _, row _ _ => by rw [zero, comp, comp_zero, comp_zero, comp_zero, comp_zero]; rfl
| _, _, of_cat _, column _ _ => by rw [zero, zero, comp, comp_zero, zero_add, comp_zero, zero]
| _, _, sum _ _, column _ _ => by rw [zero, zero, comp, comp_zero, zero_add, comp_zero,
  comp_zero, zero_add, comp_zero]
| _, _, of_cat _, scalar _ => by rw [zero, comp]
| _, _, sum _ _, scalar _ => by rw [zero, comp, comp_zero, comp_zero]; rfl
termination_by comp_zero X Y Z f => (size X, size Y, size Z)

@[simp] theorem zero_comp : {X Y Z : biprod C} → (f : hom Y Z) →
  comp (@zero _ _ X Y) f = zero
| of_cat _, _, _, hom.zero _ _ => by rw [zero, comp]
| of_cat _, _, _, matrix _ _ _ _ => by
  rw [zero, comp, zero_comp, zero_add, zero_comp, zero_comp, zero_add, zero_comp]; rfl
| sum _ _, _, _, matrix _ _ _ _ => by
  rw [zero, comp, zero, zero_comp, zero_add, zero_comp, zero_comp, zero_add, zero_comp,
     zero_comp, zero_add, zero_comp, zero_comp, zero_add, zero_comp]
| of_cat _, _, _, row _ _ => by rw [zero, zero, comp, zero_comp, zero_add, zero_comp, zero]
| sum _ _, _, _, row _ _ => by rw [zero, zero, comp, zero_comp, zero_add, zero_comp, zero_comp,
  zero_add, zero_comp]
| of_cat _, _, _, column _ _ => by rw [zero, zero, comp, zero]
| sum _ _, _, _, column _ _ => by rw [zero, comp, zero_comp, zero_comp, zero_comp, zero_comp, zero]
| of_cat _, _, _, scalar _ => by rw [zero, comp]
| sum _ _, _, _, scalar _ => by rw [zero, comp, zero_comp, zero_comp]; rfl
| sum _ _, _, _, hom.zero _ _ => rfl
termination_by zero_comp X Y Z f => (size X, size Y, size Z)

def inl : {X Y : biprod C} → hom X (sum X Y)
| of_cat _, _ => column (scalar (𝟙 _)) zero
| sum _ _, _ => matrix inl zero zero zero

def inr : {X Y : biprod C} → hom Y (sum X Y)
| _, of_cat _ => column zero (scalar (𝟙 _))
| _, sum _ _ => matrix zero zero zero inr

def fst : {X Y : biprod C} → hom (sum X Y) X
| of_cat _, _ => row (scalar (𝟙 _)) zero
| sum _ _, _ => matrix fst zero zero zero

def snd : {X Y : biprod C} → hom (sum X Y) Y
| _, of_cat _ => row zero (scalar (𝟙 _))
| _, sum _ _ => matrix zero zero zero snd

theorem coprod_mk_comp_inl : {W X Y Z : biprod C} → (f : hom X Z) → (g : hom Y Z) →
  comp (coprod_mk f g) (inl : hom Z (sum Z W)) =
  coprod_mk (comp f inl) (comp g inl)
| _, _, _, of_cat _, f, g => by
  rw [inl, coprod_mk, comp]
| _, _, _, sum _ _, column a b, column c d => _
| _, _, _, sum _ _, column a b, matrix c d e f => _
| _, _, _, sum _ _, matrix a b c d, matrix e f g h => _
| _, _, _, sum _ _, matrix a b c d, column e f => _

-- | comp_inr_coprod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Z) (g : norm_hom2 Y Z) :
--   norm_hom2.rel (@norm_hom2.comp_inr _ _ _ Y _ (norm_hom2.coprod_mk f g))
--     (norm_hom2.coprod_mk f.comp_inr g.comp_inr)
-- | fst_comp_prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
--   norm_hom2.rel (@norm_hom2.fst_comp _ _ _ Y _ (norm_hom2.prod_mk f g))
--     (norm_hom2.prod_mk f.fst_comp g.fst_comp)
-- | snd_comp_prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
--   norm_hom2.rel (@norm_hom2.snd_comp _ _ Y _ _ (norm_hom2.prod_mk f g))
--     (norm_hom2.prod_mk f.snd_comp g.snd_comp)
-- | fst_comp_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
--   norm_hom2.rel (f.fst_comp.comp_inl : norm_hom2 (prod X W) (coprod Y Z)) f.comp_inl.fst_comp
-- | snd_comp_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
--   norm_hom2.rel (f.snd_comp.comp_inl : norm_hom2 (prod W X) (coprod Y Z)) f.comp_inl.snd_comp
-- | fst_comp_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
--   norm_hom2.rel (f.fst_comp.comp_inr : norm_hom2 (prod X W) (coprod Z Y)) f.comp_inr.fst_comp
-- | snd_comp_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
--   norm_hom2.rel (f.snd_comp.comp_inr : norm_hom2 (prod W X) (coprod Z Y)) f.comp_inr.snd_comp


end biprod
