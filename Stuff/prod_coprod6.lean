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
| prod : (Bool → prod_coprod) → prod_coprod
| coprod : (Bool → prod_coprod) → prod_coprod
| top : prod_coprod
| bot : prod_coprod

namespace prod_coprod

variable {C}

@[simp] def size : prod_coprod C → Nat
| of_cat' _ => 1
| top => 1
| prod X => size (X true) + size (X false) + 1
| coprod X => size (X true) + size (X false) + 1
| bot => 1

inductive syn : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} : (X ⟶ Y) → syn (of_cat' X) (of_cat' Y)
| prod_mk {X : prod_coprod C} {Y : Bool → prod_coprod C} :
  ((i : Bool) → syn X (Y i)) → syn X (prod Y)
| coprod_mk {X : Bool → prod_coprod C} {Y : prod_coprod C} :
  ((i : Bool) → syn (X i) Y) → syn (coprod X) Y
| top_mk (X : prod_coprod C) : syn X top
| bot_mk (X : prod_coprod C) : syn bot X
| proj {X : Bool → prod_coprod C} (i : Bool) : syn (prod X) (X i)
| inj {X : Bool → prod_coprod C} (i : Bool) : syn (X i) (coprod X)
| id (X : prod_coprod C) : syn X X
| comp {X Y Z : prod_coprod C} : syn X Y → syn Y Z → syn X Z

namespace syn

inductive rel : {X Y : prod_coprod C} → syn X Y → syn X Y → Type
| refl {X Y : prod_coprod C} (f : syn X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : syn X Y} : rel g f → rel f g
| trans {X Y : prod_coprod C} {f g h : syn X Y} : rel f g → rel g h → rel f h
| prod_mk_congr {X : prod_coprod C} {Y : Bool → prod_coprod C}
  {f₁ f₂ : (i : Bool) → syn X (Y i)}
  (h : ∀ (i : Bool), rel (f₁ i) (f₂ i)) :
  rel (prod_mk f₁) (prod_mk f₂)
| coprod_mk_congr {X : Bool → prod_coprod C} {Y : prod_coprod C}
  {f₁ f₂ : (i : Bool) → syn (X i) Y}
  (h : ∀ (i : Bool), rel (f₁ i) (f₂ i)) :
  rel (coprod_mk f₁) (coprod_mk f₂)
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : syn X Y} {g₁ g₂ : syn Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| id_comp {X Y : prod_coprod C} (f : syn X Y) : rel ((id X).comp f) f
| comp_id {X Y : prod_coprod C} (f : syn X Y) : rel (f.comp (id Y)) f
| assoc {W X Y Z : prod_coprod C} (f : syn W X) (g : syn X Y) (h : syn Y Z) :
  rel (f.comp (g.comp h)) ((f.comp g).comp h)
| of_cat_id {X : C} : rel (of_cat (𝟙 X)) (id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : rel (of_cat (f ≫ g))
  ((of_cat f).comp (of_cat g))
| prod_eta {X : prod_coprod C} {Y : Bool → prod_coprod C} (f : syn X (prod Y)) :
  rel (prod_mk (λ i => f.comp (proj i))) f
| coprod_eta {X : Bool → prod_coprod C} {Y : prod_coprod C} (f : syn (coprod X) Y) :
  rel (coprod_mk (λ i => (inj i).comp f)) f
| prod_mk_proj {X : prod_coprod C} {Y : Bool → prod_coprod C}
  (f : (i : Bool) → syn X (Y i)) (i : Bool) :
  rel ((prod_mk f).comp (proj i)) (f i)
| coprod_mk_inj {X : Bool → prod_coprod C} {Y : prod_coprod C}
  (f : (i : Bool) → syn (X i) Y) :
  rel ((inj i).comp (coprod_mk f)) (f i)

end syn

mutual

inductive syn2' : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} : (X ⟶ Y) → syn2' (of_cat' X) (of_cat' Y)
| prod_mk {X : prod_coprod C} {Y : Bool → prod_coprod C} :
  ((i : Bool) → syn2 X (Y i)) → syn2' X (prod Y)
| coprod_mk {X : Bool → prod_coprod C} {Y : prod_coprod C} :
  ((i : Bool) → syn2 (X i) Y) → syn2' (coprod X) Y
| top_mk (X : prod_coprod C) : syn2' X top
| bot_mk (X : prod_coprod C) : syn2' bot X
| proj {X : Bool → prod_coprod C} (i : Bool) : syn2' (prod X) (X i)
| inj {X : Bool → prod_coprod C} (i : Bool) : syn2' (X i) (coprod X)
| id (X : prod_coprod C) : syn2' X X

inductive syn2 : (X Y : prod_coprod C) → Type
| of' : {X Y : prod_coprod C} → syn2' X Y → syn2 X Y
| comp' : {X Y Z : prod_coprod C} → syn2' X Y → syn2 Y Z → syn2 X Z

end

namespace syn2

def prod_mk {X : prod_coprod C} {Y : Bool → prod_coprod C}
  (f : (i : Bool) → syn2 X (Y i)) : syn2 X (prod Y) :=
syn2.of' (syn2'.prod_mk f)

def coprod_mk {X : Bool → prod_coprod C} {Y : prod_coprod C}
  (f : (i : Bool) → syn2 (X i) Y) : syn2 (coprod X) Y :=
syn2.of' (syn2'.coprod_mk f)

def bot_mk (X : prod_coprod C) : syn2 bot X :=
syn2.of' (syn2'.bot_mk X)

def top_mk (X : prod_coprod C) : syn2 X top :=
syn2.of' (syn2'.top_mk X)

def proj {X : Bool → prod_coprod C} (i : Bool) : syn2 (prod X) (X i) :=
syn2.of' (syn2'.proj i)

def inj {X : Bool → prod_coprod C} (i : Bool) : syn2 (X i) (coprod X) :=
syn2.of' (syn2'.inj i)

def comp : {X Y Z : prod_coprod C} → syn2 X Y → syn2 Y Z → syn2 X Z
| _, _, _, syn2.of' f, g => syn2.comp' f g
| _, _, _, syn2.comp' f g, h => syn2.comp' f (comp g h)

inductive rel : {X Y : prod_coprod C} → syn2 X Y → syn2 X Y → Type
| refl {X Y : prod_coprod C} (f : syn2 X Y) : rel f f
-- | symm {X Y : prod_coprod C} {f g : syn2 X Y} : rel g f → rel f g
-- | trans {X Y : prod_coprod C} {f g h : syn2 X Y} : rel f g → rel g h → rel f h
-- | prod_mk_congr {X : prod_coprod C} {Y : Bool → prod_coprod C}
--   {f₁ f₂ : (i : Bool) → syn2 X (Y i)}
--   (h : ∀ (i : Bool), rel (f₁ i) (f₂ i)) :
--   rel (prod_mk f₁) (prod_mk f₂)
-- | coprod_mk_congr {X : Bool → prod_coprod C} {Y : prod_coprod C}
--   {f₁ f₂ : (i : Bool) → syn2 (X i) Y}
--   (h : ∀ (i : Bool), rel (f₁ i) (f₂ i)) :
--   rel (coprod_mk f₁) (coprod_mk f₂)
-- | comp_congr {X Y Z : prod_coprod C}
--   {f₁ f₂ : syn2 X Y} {g₁ g₂ : syn2 Y Z} : rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| top_mk {X : prod_coprod C} (f : syn2 X top) : rel f (top_mk X)
| bot_mk {X : prod_coprod C} (f : syn2 bot X) : rel f (bot_mk X)
| prod_eta {X : prod_coprod C} {Y : Bool → prod_coprod C} {f₁ : syn2 X (prod Y)}
  {f₂ : (i : Bool) → syn2 X (Y i)} :
  (∀ i, rel (syn2.comp f₁ (proj i)) (f₂ i)) → rel f₁ (prod_mk (λ i => f₂ i))
| coprod_eta {X : Bool → prod_coprod C} {Y : prod_coprod C} {f₁ : syn2 (coprod X) Y}
  {f₂ : (i : Bool) → syn2 (X i) Y} :
  (∀ i, rel (syn2.comp (inj i) f₁) (f₂ i)) → rel f₁ (coprod_mk (λ i => f₂ i))
| of_cat_id {X : C} : rel (syn2.of' (syn2'.id (of_cat' X))) (syn2.of' (syn2'.of_cat (𝟙 X)))
-- | prod_mk_coprod_mk {X Y : Bool → prod_coprod C} (f : (i j : Bool) → syn2 (X i) (Y j)) :
--   rel (coprod_mk (λ i => prod_mk (λ j => f i j))) (prod_mk (λ j => coprod_mk (λ i => f i j)))

def normalize_pair : {X Y Z : prod_coprod C} → (f : syn2' X Y) → (g : syn2' Y Z) → syn2 X Z
| _, _, top, _, _ => syn2.top_mk _
| bot, _, _, _, _ => syn2.bot_mk _
| _, _, _, f, syn2'.proj i => _

mutual

def cutelim' : {X Y : prod_coprod C} → (f : syn2' X Y) → (f' : syn2' X Y) × rel (syn2.of' f) (syn2.of' f')
| X, prod Y, f => ⟨syn2'.prod_mk (λ i => (cutelim (syn2.comp (syn2.of' f) (proj i))).1),
    rel.prod_eta (λ i => (cutelim (syn2.comp (syn2.of' f) (proj i))).2)⟩
| _, top, f => ⟨syn2'.top_mk _, rel.top_mk _⟩
| coprod X, Y, f => ⟨syn2'.coprod_mk (λ i => (cutelim (syn2.comp (inj i) (syn2.of' f))).1),
    rel.coprod_eta (λ i => (cutelim (syn2.comp (inj i) (syn2.of' f))).2)⟩
| bot, _, f => ⟨syn2'.bot_mk _, rel.bot_mk _⟩
--| of_cat' _, of_cat' _, syn2'.id _ => ⟨syn2'.of_cat (𝟙 _), rel.of_cat_id⟩
| _, _, f => ⟨f, rel.refl _⟩


def cutelim : {X Y : prod_coprod C} → (f : syn2 X Y) → (f' : syn2 X Y) × rel f f'
| X, Y, f => sorry

end

end syn2