
inductive T : Bool → Type
| mk1 : (a : Bool) → T a
| mk2 (f : Bool → Bool) (i : Bool) : T (f i)

def f : (a : Bool) → T a → Nat
| false, T.mk1 false => 0
| _, _ => 0

def f' (a : Bool) (b : T a) : Nat := by
  cases b
  cases a
  exact 0
  exact 0
  exact 0

#exit

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
-- | prod_mk_coprod_mk {X Y : Bool → prod_coprod C} (f : (i j : Bool) → syn2 (X i) (Y j)) :
--   rel (coprod_mk (λ i => prod_mk (λ j => f i j))) (prod_mk (λ j => coprod_mk (λ i => f i j)))

mutual

def cutelim' : {X Y : prod_coprod C} → (f : syn2' X Y) → (f' : syn2' X Y) × rel (syn2.of' f) (syn2.of' f')
| X, prod Y, f => ⟨syn2'.prod_mk (λ i => (cutelim (syn2.comp (syn2.of' f) (proj i))).1),
    rel.prod_eta (λ i => (cutelim (syn2.comp (syn2.of' f) (proj i))).2)⟩
| _, top, f => ⟨syn2'.top_mk _, rel.top_mk _⟩
| coprod X, Y, f => ⟨syn2'.coprod_mk (λ i => (cutelim (syn2.comp (inj i) (syn2.of' f))).1),
    rel.coprod_eta (λ i => (cutelim (syn2.comp (inj i) (syn2.of' f))).2)⟩
| bot, _, f => ⟨syn2'.bot_mk _, rel.bot_mk _⟩
| of_cat' _, of_cat' _, f =>
  match f with
  | syn2'.id _ => ⟨_, _⟩
| _, _, f => ⟨f, rel.refl _⟩


def cutelim : {X Y : prod_coprod C} → (f : syn2 X Y) → (f' : syn2 X Y) × rel f f'
| X, Y, f => sorry

end

end syn2