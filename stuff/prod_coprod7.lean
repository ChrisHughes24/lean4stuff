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

inductive syn [(X Y : C) → DecidableEq (X ⟶ Y)] : (X Y : prod_coprod C) → Type
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
| fst {X Y : prod_coprod C} : syn2' (prod X Y) X
| snd {X Y : prod_coprod C} : syn2' (prod X Y) Y
| inl {X Y : prod_coprod C} : syn2' X (coprod X Y)
| inr {X Y : prod_coprod C} : syn2' Y (coprod X Y)
| id (X : prod_coprod C) : syn2' X X

inductive syn2 : (X Y : prod_coprod C) → Type
| of' : {X Y : prod_coprod C} → syn2' X Y → syn2 X Y
| comp' : {X Y Z : prod_coprod C} → syn2 X Y → syn2' Y Z → syn2 X Z

end

mutual

def syn2'DecEq : {X Y : prod_coprod C} → DecidableEq (syn2' X Y)
| _, _, of_cat f, of_cat g => _

def syn2'DecEq : {X Y : prod_coprod C} → DecidableEq (syn2 X Y)
| _, _ => sorry

namespace syn2

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

def fst {X Y : prod_coprod C} : syn2 (prod X Y) X :=
syn2.of' syn2'.fst

def snd {X Y : prod_coprod C} : syn2 (prod X Y) Y :=
syn2.of' syn2'.snd

def inl {X Y : prod_coprod C} : syn2 X (coprod X Y) :=
syn2.of' syn2'.inl

def inr {X Y : prod_coprod C} : syn2 Y (coprod X Y) :=
syn2.of' syn2'.inr

def comp : {X Y Z : prod_coprod C} → syn2 X Y → syn2 Y Z → syn2 X Z
| _, _, _, f, syn2.of' g => syn2.comp' f g
| _, _, _, f, syn2.comp' g h => syn2.comp' (comp f g) h

mutual

unsafe def cutelim_pair : {X Y Z : prod_coprod C} → (f : syn2' X Y) → (g : syn2' Y Z) →
  syn2 X Z × Bool -- Boolean indicates if any rewrites applied
| _, _, top, _, _ => ⟨syn2.top_mk _, true⟩
| bot, _, _, _, _ => ⟨syn2.bot_mk _, true⟩
| _, _, _, syn2'.prod_mk f _, syn2'.fst => ⟨f, true⟩
| _, _, _, syn2'.prod_mk _ g, syn2'.snd => ⟨g, true⟩
| _, _, _, syn2'.inl, syn2'.coprod_mk f _ => ⟨f, true⟩
| _, _, _, syn2'.inr, syn2'.coprod_mk _ g => ⟨g, true⟩
| _, _, _, f, syn2'.prod_mk g h => ⟨syn2.prod_mk ((syn2.of' f).comp g) ((syn2.of' f).comp h),
  true⟩
| _, _, _, syn2'.coprod_mk f g, h => ⟨syn2.coprod_mk (f.comp' h) (g.comp' h), true⟩
| _, _, _, f, g => ⟨syn2.comp' (syn2.of' f) g, false⟩

unsafe def cutelim_single : {X Y : prod_coprod C} → (f : syn2' X Y) →
  syn2' X Y × Bool -- Boolean indicates if any rewrites applied
| _, top, _ => ⟨syn2'.top_mk _, true⟩
| bot, _, _ => ⟨syn2'.bot_mk _, true⟩
| _, prod _ _, f =>
  let g := cutelim (syn2.comp (syn2.of' f) fst)
  let h := cutelim (syn2.comp (syn2.of' f) snd)
  ⟨syn2'.prod_mk g h, true⟩
| coprod _ _, _, f =>
  let g := cutelim (syn2.comp inl (syn2.of' f))
  let h := cutelim (syn2.comp inr (syn2.of' f))
  ⟨syn2'.coprod_mk g h, true⟩
| of_cat' _, of_cat' _, syn2'.id _ => ⟨syn2'.of_cat (𝟙 _),  true⟩
| _, _, f => ⟨f, false⟩

unsafe def cutelim : {X Y : prod_coprod C} → (f : syn2 X Y) → syn2 X Y
| _, _, syn2.of' f =>
  let f' := cutelim_single f
  syn2.of' f'.1
| _, _, syn2.comp' f g =>
  match cutelim f with
  | syn2.of' f => (cutelim_pair f g).1
  | syn2.comp' e f =>
    match cutelim_pair f g with
    | ⟨fg, true⟩ => cutelim (e.comp fg)
    | ⟨fg, false⟩ => e.comp fg

end

mutual

unsafe def normalize_single : {X Y : prod_coprod C} → (f : syn2' X Y) → syn2 X Y
| _, _, syn2'.coprod_mk f g =>
  match normalize f, normalize g with
  | comp' f₁ f₂, comp' g₁ g₂ =>
    if f₂ = g₂
      then (syn2.coprod_mk f₁ g₂).comp' f₂
      else syn2.coprod_mk (comp' f₁ f₂) (comp' g₁ g₂)
  | f, g => syn2.coprod_mk f g
| _, _, _ => sorry

unsafe def normalize : {X Y : prod_coprod C} → (f : syn2 X Y) → syn2 X Y
| _, _, _ => sorry

end

end syn2