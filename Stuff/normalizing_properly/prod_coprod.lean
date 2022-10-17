import Stuff.normalizing_properly.category

variable (C : Type) [category C]

inductive prod_coprod : Type
| of_cat' : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod
| top : prod_coprod
| bot : prod_coprod
deriving DecidableEq

namespace prod_coprod

variable {C}

@[simp] def size : prod_coprod C → Nat
| of_cat' _ => 1
| top => 1
| prod X Y => size X + size Y + 1
| coprod X Y => size X + size Y + 1
| bot => 1

inductive syn : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} : (X ⟶ Y) → syn (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} (f : syn X Y) (g : syn X Z) :
  syn X (prod Y Z)
| coprod_mk {X Y Z : prod_coprod C} (f : syn X Z) (g : syn Y Z) :
  syn (coprod X Y) Z
| top_mk (X : prod_coprod C) : syn X top
| bot_mk (X : prod_coprod C) : syn bot X
| fst {X Y : prod_coprod C} : syn (prod X Y) X
| snd {X Y : prod_coprod C} : syn (prod X Y) Y
| inl {X Y : prod_coprod C} : syn X (coprod X Y)
| inr {X Y : prod_coprod C} : syn Y (coprod X Y)
| id (X : prod_coprod C) : syn X X
| comp {X Y Z : prod_coprod C} : syn X Y → syn Y Z → syn X Z

mutual

inductive syn2' : (X Y : prod_coprod C) → Type
| of_cat {X Y : C} : (X ⟶ Y) → syn2' (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} (f : syn2 X Y) (g : syn2 X Z) :
  syn2' X (prod Y Z)
| coprod_mk {X Y Z : prod_coprod C} (f : syn2 X Z) (g : syn2 Y Z) :
  syn2' (coprod X Y) Z
| top_mk (X : prod_coprod C) : syn2' X top
| bot_mk (X : prod_coprod C) : syn2' bot X
| fst_comp {X Y Z : prod_coprod C} (f : syn2 X Z) : syn2' (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : syn2 Y Z) : syn2' (prod X Y) Z
| comp_inl {X Y Z : prod_coprod C} (f : syn2 X Y) : syn2' X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : syn2 X Z) : syn2' X (coprod Y Z)


inductive syn2 : (X Y : prod_coprod C) → Type
| of' : {X Y : prod_coprod C} → syn2' X Y → syn2 X Y
| comp' : {X Y Z : prod_coprod C} → syn2 X Y → syn2' Y Z → syn2 X Z

end

section decEq

mutual

def syn2'BEq [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y : prod_coprod C} → syn2' X Y → syn2' X Y → Bool
| _, _, syn2'.of_cat f, syn2'.of_cat g =>
  if f = g then true else false
| _, _, syn2'.prod_mk f₁ g₁, syn2'.prod_mk f₂ g₂ =>
  (syn2BEq f₁ f₂) && (syn2BEq g₁ g₂)
| _, _, syn2'.coprod_mk f₁ g₁, syn2'.coprod_mk f₂ g₂ =>
  (syn2BEq f₁ f₂) && (syn2BEq g₁ g₂)
| _, _, @syn2'.top_mk C _ _, @syn2'.top_mk C _ _ => true
| _, _, @syn2'.bot_mk C _ _, @syn2'.bot_mk C _ _ => true
| _, _, syn2'.fst_comp f, syn2'.fst_comp g => syn2BEq f g
| _, _, syn2'.snd_comp f, syn2'.snd_comp g => syn2BEq f g
| _, _, syn2'.comp_inl f, syn2'.comp_inl g => syn2BEq f g
| _, _, syn2'.comp_inr f, syn2'.comp_inr g => syn2BEq f g
| _, _, _, _ => false

def syn2BEq [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y : prod_coprod C} → syn2 X Y → syn2 X Y → Bool
| _, _, syn2.of' f, syn2.of' g => syn2'BEq f g
| _, _, @syn2.comp' _ _ _ Y₁ _ f₁ g₁, @syn2.comp' _ _ _ Y₂ _ f₂ g₂ =>
  if hY : Y₁ = Y₂
  then by subst hY; exact (syn2BEq f₁ f₂) && (syn2'BEq g₁ g₂)
  else false
| _, _, _, _ => false

end

axiom thing' [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] {X Y : prod_coprod C}
  {f g : syn2' X Y} : syn2'BEq f g = true ↔ f = g

axiom thing [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] {X Y : prod_coprod C}
  {f g : syn2 X Y} : syn2BEq f g = true ↔ f = g

instance [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] {X Y : prod_coprod C} :
  DecidableEq (syn2' X Y) :=
λ f g : syn2' X Y =>
@decidable_of_decidable_of_iff (syn2'BEq f g = true) _ _ thing'

instance [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] {X Y : prod_coprod C} :
  DecidableEq (syn2 X Y) :=
λ f g : syn2 X Y =>
@decidable_of_decidable_of_iff (syn2BEq f g = true) _ _ thing

end decEq

namespace syn2

def of_cat {X Y : C} (f : X ⟶ Y) : syn2 (of_cat' X) (of_cat' Y) :=
syn2.of' (syn2'.of_cat f)

def prod_mk {X Y Z : prod_coprod C}
  (f : syn2 X Y) (g : syn2 X Z) : syn2 X (prod Y Z) :=
syn2.of' (syn2'.prod_mk f g)

def coprod_mk {X Y Z : prod_coprod C}
  (f : syn2 X Z) (g : syn2 Y Z) : syn2 (coprod X Y) Z :=
syn2.of' (syn2'.coprod_mk f g)

def bot_mk (X : prod_coprod C) : syn2 bot X :=
syn2.of' (syn2'.bot_mk X)

def top_mk (X : prod_coprod C) : syn2 X top :=
syn2.of' (syn2'.top_mk X)

def fst_comp {X Y Z : prod_coprod C} (f : syn2 X Z) : syn2 (prod X Y) Z :=
syn2.of' (syn2'.fst_comp f)

def snd_comp {X Y Z : prod_coprod C} (f : syn2 Y Z) : syn2 (prod X Y) Z :=
syn2.of' (syn2'.snd_comp f)

def comp_inl {X Y Z : prod_coprod C} (f : syn2 X Y) : syn2 X (coprod Y Z) :=
syn2.of' (syn2'.comp_inl f)

def comp_inr {X Y Z : prod_coprod C} (f : syn2 X Z) : syn2 X (coprod Y Z) :=
syn2.of' (syn2'.comp_inr f)

def comp : {X Y Z : prod_coprod C} → syn2 X Y → syn2 Y Z → syn2 X Z
| _, _, _, f, syn2.of' g => syn2.comp' f g
| _, _, _, f, syn2.comp' g h => syn2.comp' (comp f g) h

def id : {X : prod_coprod C} → syn2 X X
| of_cat' X => of_cat (𝟙 X)
| prod _ _ => syn2.prod_mk (syn2.fst_comp id) (syn2.snd_comp id)
| coprod _ _ => syn2.coprod_mk (syn2.comp_inl id) (syn2.comp_inr id)
| top => top_mk _
| bot => bot_mk _

def fst {X Y : prod_coprod C} : syn2 (prod X Y) X :=
syn2.fst_comp syn2.id

def snd {X Y : prod_coprod C} : syn2 (prod X Y) Y :=
syn2.snd_comp syn2.id

def inl {X Y : prod_coprod C} : syn2 X (coprod X Y) :=
syn2.comp_inl syn2.id

def inr {X Y : prod_coprod C} : syn2 Y (coprod X Y) :=
syn2.comp_inr syn2.id

mutual

unsafe def cutelim_single [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y : prod_coprod C} → (f : syn2' X Y) →
  syn2' X Y × Bool -- Boolean indicates if any rewrites applied
| _, _, syn2'.prod_mk f g =>
  match cutelim f, cutelim g with
  | ⟨f, b₁⟩, ⟨g, b₂⟩ => ⟨syn2'.prod_mk f g, b₁ || b₂⟩
| _, _, syn2'.coprod_mk f g =>
  match cutelim f, cutelim g with
  | ⟨f, b₁⟩, ⟨g, b₂⟩ => ⟨syn2'.coprod_mk f g, b₁ || b₂⟩
| _, _, f => ⟨f, false⟩

/-- eliminates cuts from f ∘ g assuming f and g are both cut eliminated. -/
unsafe def cutelim_pair [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y Z : prod_coprod C} → (f : syn2' X Y) → (g : syn2' Y Z) →
  syn2 X Z × Bool -- Boolean indicates if any rewrites applied
| _, _, top, _, _ => ⟨syn2.top_mk _, true⟩
| bot, _, _, _, _ => ⟨syn2.bot_mk _, true⟩
| _, _, _, syn2'.of_cat f, syn2'.of_cat g => ⟨syn2.of' (syn2'.of_cat (f ≫ g)), true⟩
| _, _, _, syn2'.prod_mk f _, syn2'.fst_comp g => ⟨(cutelim (f.comp g)).1, true⟩
| _, _, _, syn2'.prod_mk _ f, syn2'.snd_comp g => ⟨(cutelim (f.comp g)).1, true⟩
| _, _, _, syn2'.comp_inl f, syn2'.coprod_mk g _ => ⟨(cutelim (f.comp g)).1, true⟩
| _, _, _, syn2'.comp_inr f, syn2'.coprod_mk _ g => ⟨(cutelim (f.comp g)).1, true⟩
| _, _, _, f, syn2'.prod_mk g h =>
  ⟨syn2.prod_mk (cutelim ((syn2.of' f).comp g)).1
                (cutelim ((syn2.of' f).comp h)).1,
  true⟩
| _, _, _, syn2'.coprod_mk f g, h =>
  ⟨syn2.coprod_mk (cutelim (f.comp' h)).1 (cutelim (g.comp' h)).1,
    true⟩
| of_cat' X, of_cat' Y, _, syn2'.of_cat f, g =>
  if h : X = Y
  then if f = (by rw [h]; exact 𝟙 Y)
    then by rw [h]; exact ⟨syn2.of' g, true⟩
    else ⟨syn2.comp' (syn2.of' (syn2'.of_cat f)) g, false⟩
  else ⟨syn2.comp' (syn2.of' (syn2'.of_cat f)) g, false⟩
| _, of_cat' X, of_cat' Y, f, syn2'.of_cat g =>
  if h : Y = X
  then if g = (by rw [h]; exact 𝟙 X)
    then by rw [h]; exact ⟨syn2.of' f, true⟩
    else ⟨syn2.comp' (syn2.of' f) (syn2'.of_cat g), false⟩
  else ⟨syn2.comp' (syn2.of' f) (syn2'.of_cat g), false⟩
| _, _, _, f, g => ⟨syn2.comp' (syn2.of' f) g, false⟩

unsafe def cutelim [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y : prod_coprod C} → (f : syn2 X Y) → syn2 X Y × Bool
| _, _, syn2.of' f =>
  let f' := cutelim_single f
  ⟨syn2.of' f'.1, f'.2⟩
| _, _, syn2.comp' f g =>
  match cutelim f, cutelim_single g with
  | ⟨syn2.of' f, b₁⟩, ⟨g, b₂⟩ =>
    match cutelim_pair f g with
    | ⟨fg, b₃⟩ => ⟨fg, b₁ || b₂ || b₃⟩
  | ⟨syn2.comp' e f, b₁⟩, ⟨g, b₂⟩ =>
    match cutelim_pair f g with
    | ⟨fg, true⟩ => ⟨(cutelim (e.comp fg)).1, true⟩
    | ⟨fg, false⟩ => ⟨e.comp fg, b₁ || b₂⟩

end

mutual

/- Normalizing cut eliminated terms. -/

unsafe def normalize_single_ce [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y : prod_coprod C} → (f : syn2' X Y) → syn2 X Y × Bool
| coprod X Y, Z, syn2'.coprod_mk f g =>
  match X, Y, Z, normalize_ce f, normalize_ce g with
  | _, _, _, (@comp' _ _ _ Y₁ Z f₁ f₂, _), (@comp' _ _ _ Y₂ _ g₁ g₂, _) =>
    if h : (⟨Y₁, f₂⟩ : Σ (Y : prod_coprod C), syn2' Y Z) = ⟨Y₂, g₂⟩
      then by
        injection h with h₁ h₂
        subst h₁
        exact ((normalize_ce ((syn2.coprod_mk f₁ g₁).comp' f₂)).1, true)
      else (syn2.coprod_mk (comp' f₁ f₂) (comp' g₁ g₂), false)
  | _, _, _, (syn2.of' (syn2'.comp_inl f), _), (syn2.of' (syn2'.comp_inl g), _) => ((syn2.coprod_mk f g).comp_inl, true)
  | _, _, _, (syn2.of' (syn2'.comp_inr f), _), (syn2.of' (syn2'.comp_inr g), _) => ((syn2.coprod_mk f g).comp_inr, true)
  | _, _, _, (syn2.of' (syn2'.prod_mk f g), _), (syn2.of' (syn2'.prod_mk h i), _) =>
    (syn2.prod_mk (syn2.coprod_mk f h) (syn2.coprod_mk g i), true)
  | _, _, _, (f, b₁), (g, b₂) => (syn2.coprod_mk f g, b₁ || b₂)
| _, _, syn2'.fst_comp f =>
  match normalize_ce f with
  | (syn2.of' (syn2'.prod_mk f g), _) => (syn2.prod_mk (syn2.fst_comp f) (syn2.fst_comp g), true)
  | (syn2.of' (syn2'.comp_inl f), _) => (syn2.comp_inl (syn2.fst_comp f), true)
  | (syn2.of' (syn2'.comp_inr f), _) => (syn2.comp_inr (syn2.fst_comp f), true)
  | (syn2.comp' f g, _) => ((normalize_ce (syn2.comp' (fst_comp f) g)).1, true)
  | (e, b) => (e.fst_comp, b)
| _, _, syn2'.snd_comp f =>
  match normalize_ce f with
  | (syn2.of' (syn2'.prod_mk f g), _) => (syn2.prod_mk (syn2.snd_comp f) (syn2.snd_comp g), true)
  | (syn2.of' (syn2'.comp_inl f), _) => (syn2.comp_inl (syn2.snd_comp f), true)
  | (syn2.of' (syn2'.comp_inr f), _) => (syn2.comp_inr (syn2.snd_comp f), true)
  | (syn2.comp' f g, _) => ((normalize_ce (syn2.comp' (snd_comp f) g)).1, true)
  | (e, b) => (e.snd_comp, b)
| _, _, syn2'.prod_mk f g =>
  match normalize_ce f, normalize_ce g with
  | (f, false), (g, false) => (syn2.prod_mk f g, false)
  | (f, _), (g, _) => (syn2.prod_mk f g, true)
| _, _, f => (syn2.of' f, false)

unsafe def normalize_pair_ce [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y Z : prod_coprod C} → (f : syn2' X Y) →
  (g : syn2' Y Z) → syn2 X Z × Bool
| _, _, _, f, syn2'.prod_mk g h =>
  ⟨syn2.prod_mk (normalize_ce ((syn2.of' f).comp g)).1 (normalize_ce ((syn2.of' f).comp h)).1, true⟩
| _, _, _, f, syn2'.comp_inl g => ((normalize_ce (syn2.comp (syn2.of' f) g)).1.comp_inl, true)
| _, _, _, f, syn2'.comp_inr g => ((normalize_ce (syn2.comp (syn2.of' f) g)).1.comp_inr, true)
| _, _, _, f, g =>
  match normalize_single_ce f, normalize_single_ce g with
  | (f, false), (g, false) => ⟨syn2.comp f g, false⟩
  | (f, _), (g, _) => ⟨syn2.comp f g, true⟩

unsafe def normalize_ce [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)] :
  {X Y : prod_coprod C} → (f : syn2 X Y) → syn2 X Y × Bool
| _, _, syn2.of' f => normalize_single_ce f
| _, _, syn2.comp' f g =>
  match normalize_ce f with
  | (syn2.of' f, b) =>
    let n := normalize_pair_ce f g
    (n.1, b || n.2)
  | (syn2.comp' e f, b) =>
    match normalize_pair_ce f g with
    | ⟨fg, true⟩ => let n := normalize_ce (e.comp fg)
      (n.1, b || n.2)
    | ⟨fg, false⟩ => (e.comp fg, false)

end

unsafe def normalize [DecidableEq C]
  [(X Y : C) → DecidableEq (X ⟶ Y)]
  {X Y : prod_coprod C} (s : syn2 X Y) : syn2 X Y :=
(normalize_ce (cutelim s).1).1

def of_syn : {X Y : prod_coprod C} → (f : syn X Y) → syn2 X Y
| _, _, syn.of_cat f => syn2.of' (syn2'.of_cat f)
| _, _, syn.comp f g => comp (of_syn f) (of_syn g)
| _, _, syn.id _ => syn2.id
| _, _, syn.inr => syn2.inr
| _, _, syn.inl => syn2.inl
| _, _, syn.fst => syn2.fst
| _, _, syn.snd => syn2.snd
| _, _, syn.bot_mk _ => syn2.bot_mk _
| _, _, syn.top_mk _ => syn2.top_mk _
| _, _, syn.coprod_mk f g => syn2.coprod_mk (of_syn f) (of_syn g)
| _, _, syn.prod_mk f g => syn2.prod_mk (of_syn f) (of_syn g)

end syn2

namespace syn

unsafe def beq [DecidableEq C] [(X Y : C) → DecidableEq (X ⟶ Y)]
  {X Y : prod_coprod C} (f g : syn X Y) : Bool :=
decide (syn2.normalize (syn2.of_syn f) = syn2.normalize (syn2.of_syn g))

end syn