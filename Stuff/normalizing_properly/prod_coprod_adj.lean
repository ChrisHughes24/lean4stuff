import Mathlib.Tactic.Have

structure Cat : Type :=
( name : String )
deriving DecidableEq

structure FuncVar (C D : Cat) : Type :=
(name : String)
deriving DecidableEq

inductive Func : Cat → Cat → Type
| id (C : Cat) : Func C C
| comp' {C D E : Cat} : FuncVar C D → Func D E → Func C E
deriving DecidableEq

def FuncVar.toFunc {C D : Cat} (F : FuncVar C D) : Func C D :=
Func.comp' F $ Func.id _

def Func.comp : {C D E : Cat} → Func C D → Func D E → Func C E
| _, _, _, Func.id _, G => G
| _, _, _, Func.comp' F G, H => Func.comp' F (comp G H)

structure FData : Type :=
( rel {C D : Cat} : Func C D → Func C D → Prop )
[ decidRel {C D : Cat} : DecidableRel (@rel C D) ]
( refl {C D : Cat} (F : Func C D) : rel F F )
( symm {C D : Cat} {F G : Func C D} : rel G F → rel F G )
( trans {C D : Cat} {F G H : Func C D} : rel F G → rel G H → rel F H )
( rel_comp {C D E : Cat} {F₁ F₂ : Func C D} {G₁ G₂ : Func D E} :
  rel F₁ F₂ → rel G₁ G₂ → rel (F₁.comp G₁) (F₂.comp G₂) )
( hasRAdj {C D : Cat} : Func C D → Prop )
[ decidHasRAdj {C D : Cat} (F : Func C D): Decidable (hasRAdj F) ]
( hasRAdjCompLeft {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
  rel F (G.comp H) → hasRAdj F → hasRAdj G )
( hasRAdjCompRight {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
  rel F (G.comp H) → hasRAdj F → hasRAdj H )
( hasLAdj {C D : Cat} : Func C D → Prop )
[ decidHasLAdj {C D : Cat} (F : Func C D): Decidable (hasLAdj F) ]
( hasLAdjCompLeft {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
  rel F (G.comp H) → hasLAdj F → hasLAdj G )
( hasLAdjCompRight {C D E : Cat} (F : Func C E) (G : Func C D) (H : Func D E) :
  rel F (G.comp H) → hasLAdj F → hasLAdj H )

attribute [instance] FData.decidRel FData.decidHasRAdj FData.decidHasLAdj

def FuncVar.hasRAdj {C D : Cat} (d : FData) (F : FuncVar C D) : Prop :=
d.hasRAdj F.toFunc

instance {C D : Cat} (d : FData) (F : FuncVar C D) : Decidable (F.hasRAdj d) :=
d.decidHasRAdj _

def FuncVar.hasLAdj {C D : Cat} (d : FData) (F : FuncVar C D) : Prop :=
d.hasLAdj F.toFunc

instance {C D : Cat} (d : FData) (F : FuncVar C D) : Decidable (F.hasLAdj d) :=
d.decidHasLAdj _

inductive Obj (d : FData) : Cat → Type
| Ovar : String → Obj d C
| prod : Obj d C → Obj d C → Obj d C
| coprod : Obj d C → Obj d C → Obj d C
| app {C D : Cat} : FuncVar C D → Obj d C → Obj d D
| rAdjApp {C D : Cat} (F : FuncVar C D) : F.hasRAdj d → Obj d D → Obj d C
| lAdjApp {C D : Cat} (F : FuncVar C D) : F.hasLAdj d → Obj d D → Obj d C
| top : Obj d C
| bot : Obj d C
deriving DecidableEq

namespace Obj

variable {d : FData}

inductive syn : {C : Cat} → (X Y : Obj d C) → Type
| var {X Y : Obj d C} : String → syn X Y
| prod_mk {X Y Z : Obj d C} (f : syn X Y) (g : syn X Z) :
  syn X (prod Y Z)
| coprod_mk {X Y Z : Obj d C} (f : syn X Z) (g : syn Y Z) :
  syn (coprod X Y) Z
| top_mk (X : Obj d C) : syn X top
| bot_mk (X : Obj d C) : syn bot X
| fst {X Y : Obj d C} : syn (prod X Y) X
| snd {X Y : Obj d C} : syn (prod X Y) Y
| inl {X Y : Obj d C} : syn X (coprod X Y)
| inr {X Y : Obj d C} : syn Y (coprod X Y)
| map {X Y : Obj d C} (F : FuncVar C D) (f : syn X Y) : syn (app F X) (app F Y)
| rAdjMap {C D : Cat} {X Y : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) (f : syn X Y) :
  syn (rAdjApp F hF X) (rAdjApp F hF Y)
| counit {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) :
  syn (app F (rAdjApp F hF X)) X
| restrict {C D : Cat} {X : Obj d C} {Y : Obj d D} {F : FuncVar C D} (hF : F.hasRAdj d)
  (f : syn (app F X) Y) : syn X (rAdjApp F hF Y)
| lAdjMap {C D : Cat} {X Y : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) (f : syn X Y) :
  syn (lAdjApp F hF X) (lAdjApp F hF Y)
| unit {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) :
  syn X (app F (lAdjApp F hF X))
| extend {C D : Cat} {X : Obj d D} {Y : Obj d C} {F : FuncVar C D} (hF : F.hasLAdj d)
  (f : syn X (app F Y)) : syn (lAdjApp F hF X) Y
| id (X : Obj d C) : syn X X
| comp {X Y Z : Obj d C} : syn X Y → syn Y Z → syn X Z

def expandProds : {C : Cat} → Obj d C → Obj d C
| _, Ovar X => Ovar X
| _, prod X Y => prod (expandProds X) (expandProds Y)
| _, coprod X Y => coprod (expandProds X) (expandProds Y)
| _, app F (prod X Y) =>
  if F.hasLAdj d then
    prod (expandProds (app F X)) (expandProds (app F Y))
  else app F (expandProds (prod X Y))
| _, app F top =>
  if F.hasLAdj d then top else app F top
| _, app F (coprod X Y) =>
  if F.hasRAdj d then
    coprod (expandProds (app F X)) (expandProds (app F Y))
  else app F (expandProds (coprod X Y))
| _, app F bot =>
  if F.hasRAdj d then bot else app F bot
| _, app F X => app F (expandProds X)
| _, rAdjApp F hF X => rAdjApp F hF (expandProds X)
| _, lAdjApp F hF X => lAdjApp F hF (expandProds X)
| _, top => top
| _, bot => bot

-- def toFactorProds : {C : Cat} → {X Y : Obj d C} → syn X Y → syn (expandProds X) (expandProds Y)
-- | _, _, _, syn.var X => syn.var X
-- | _, _, _, syn.prod_mk f g =>
--   by rw [expandProds]; exact syn.prod_mk (toFactorProds f) (toFactorProds g)
-- | _, _, _, syn.coprod_mk f g =>
--   by rw [expandProds]; exact syn.coprod_mk (toFactorProds f) (toFactorProds g)
-- | _, _, _, syn.top_mk X => by rw [expandProds]; exact syn.top_mk _
-- | _, _, _, syn.bot_mk X => by rw [expandProds]; exact syn.bot_mk _
-- | _, _, _, syn.fst => by rw [expandProds]; exact syn.fst
-- | _, _, _, syn.snd => by rw [expandProds]; exact syn.snd
-- | _, _, _, syn.inl => by rw [expandProds]; exact syn.inl
-- | _, _, _, syn.inr => by rw [expandProds]; exact syn.inr
-- | _, _, _, syn.comp f g => syn.comp (toFactorProds f) (toFactorProds g)
-- | _, _, _, syn.id _ => syn.id _
-- | _, _, _, syn.lAdjMap F hF f => by rw [expandProds]; exact syn.lAdjMap F hF (toFactorProds f)
-- | _, _, _, syn.extend hF f => by rw [expandProds]; exact syn.extend hF (toFactorProds f)

inductive syn2'_var_aux : {C : Cat} → (X Y : Obj d C) → Type
| var {X Y : Obj d C} : String → syn2'_var_aux X Y
| comp_fst {X Y Z : Obj d C} : syn2'_var_aux X (prod Y Z) → syn2'_var_aux X Y
| comp_snd {X Y Z : Obj d C} : syn2'_var_aux X (prod Y Z) → syn2'_var_aux X Z
| inl_comp {X Y Z : Obj d C} : syn2'_var_aux (coprod X Y) Z → syn2'_var_aux X Z
| inr_comp {X Y Z : Obj d C} : syn2'_var_aux (coprod X Y) Z → syn2'_var_aux Y Z
| unit_comp {C D : Cat} {X : Obj d D} {Y : Obj d C} (F : FuncVar C D) (hF : F.hasLAdj d) :
  syn2'_var_aux (lAdjApp F hF X) Y → syn2'_var_aux X (app F Y)
| comp_counit {C D : Cat} {X : Obj d C} {Y : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) :
  syn2'_var_aux X (rAdjApp F hF Y) → syn2'_var_aux (app F X) Y
| expand_prods {C : Cat} {X Y : Obj d C} : syn2'_var_aux X Y →
  syn2'_var_aux (expandProds X) (expandProds Y)

def syn2'_var_aux_to_var : {C : Cat} → {X Y : Obj d C} →
  syn2'_var_aux X Y → (C : Cat) × (_ _ : Obj d C) × String
| C, X, Y, syn2'_var_aux.var s => ⟨C, X, Y, s⟩
| _, _, _, syn2'_var_aux.comp_fst f => syn2'_var_aux_to_var f
| _, _, _, syn2'_var_aux.comp_snd f => syn2'_var_aux_to_var f
| _, _, _, syn2'_var_aux.inl_comp f => syn2'_var_aux_to_var f
| _, _, _, syn2'_var_aux.inr_comp f => syn2'_var_aux_to_var f
| _, _, _, syn2'_var_aux.unit_comp _ _ f => syn2'_var_aux_to_var f
| _, _, _, syn2'_var_aux.comp_counit _ _ f => syn2'_var_aux_to_var f
| _, _, _, syn2'_var_aux.expand_prods f => syn2'_var_aux_to_var f

instance syn2'_var_aux_DecidableEq : {C : Cat} → {X Y : Obj d C} →
  DecidableEq (syn2'_var_aux X Y)
| C, X, Y, syn2'_var_aux.var s, syn2'_var_aux.var t =>
  if hst : s = t then isTrue (by rw [hst]) else isFalse (by intro h; injection h; contradiction)
| C, X, Y, syn2'_var_aux.comp_fst f, syn2'_var_aux.comp_fst g =>
  by letI := syn2'_var_aux_DecidableEq f g;elan

  if hfg : f = g then isTrue (by rw [hfg]) else isFalse (by intro h; injection h; contradiction)




inductive isnt_limity : {C : Cat} → (X : Obj d C) → Prop
| Ovar {X : String} : isnt_limity (Ovar X)
| coprod (X Y : Obj d C) : isnt_limity (coprod X Y)
| app {C D : Cat} {X : Obj d C} {Y : Obj d D} (F : FuncVar C D) : isnt_limity (app F X)
| lAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) :
  isnt_limity (lAdjApp F hF X)
| bot : isnt_limity bot

inductive isnt_limit : {C : Cat} → (X : Obj d C) → Prop
| Ovar {X : String} : isnt_limit (Ovar X)
| coprod (X Y : Obj d C) : isnt_limit (coprod X Y)
| app {C D : Cat} {X : Obj d C} {Y : Obj d D} (F : FuncVar C D) : isnt_limit (app F X)
| lAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) :
  isnt_limit (lAdjApp F hF X)
| rAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) :
  isnt_limit (rAdjApp F hF X)
| bot : isnt_limit bot

inductive isnt_colimity : {C : Cat} → (X : Obj d C) → Prop
| Ovar {X : String} : isnt_colimity (Ovar X)
| prod (X Y : Obj d C) : isnt_colimity (prod X Y)
| app {C D : Cat} {X : Obj d C} {Y : Obj d D} (F : FuncVar C D) : isnt_colimity (app F X)
| rAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) :
  isnt_colimity (rAdjApp F hF X)
| top : isnt_colimity top


inductive isnt_colimit : {C : Cat} → (X : Obj d C) → Prop
| Ovar {X : String} : isnt_colimit (Ovar X)
| prod (X Y : Obj d C) : isnt_colimit (prod X Y)
| app {C D : Cat} {X : Obj d C} {Y : Obj d D} (F : FuncVar C D) : isnt_colimit (app F X)
| rAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) :
  isnt_colimit (rAdjApp F hF X)
| lAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) :
  isnt_colimit (lAdjApp F hF X)
| top : isnt_colimit top

inductive isExpanded : {C : Cat} → (X : Obj d C) → Prop
| Ovar {X : String} : isExpanded (Ovar X)
| prod (X Y : Obj d C) : isExpanded X → isExpanded Y → isExpanded (prod X Y)
| coprod (X Y : Obj d C) : isExpanded X → isExpanded Y → isExpanded (coprod X Y)
| top : isExpanded top
| bot : isExpanded bot
| rAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) : isExpanded X →
  isExpanded (rAdjApp F hF X)
| lAdjApp {C D : Cat} {X : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) : isExpanded X →
  isExpanded (lAdjApp F hF X)
| appNotColimitNotLAdj {C D : Cat} {X : Obj d C} (F : FuncVar C D) : isnt_colimit X → ¬F.hasLAdj d →
  isExpanded X → isExpanded (app F X)
| appNotLimitNotRAdj {C D : Cat} {X : Obj d C} (F : FuncVar C D) : isnt_limit X → ¬F.hasRAdj d →
  isExpanded X → isExpanded (app F X)
| appNotLAdjNotRAdj {C D : Cat} {X : Obj d C} (F : FuncVar C D) : ¬F.hasLAdj d → ¬F.hasRAdj d →
  isExpanded X → isExpanded (app F X)
| appNotLimitNotColimit {C D : Cat} {X : Obj d C} (F : FuncVar C D) : isnt_limit X → isnt_colimit X →
  isExpanded X → isExpanded (app F X)

/-- No vars into prods, terminals or Radj, or out of coprods, initials or rAdjs. Every
  var between prodFactors -/
inductive syn2'_var : (X Y : Obj d C) → Type
| mk_var {X Y : Obj d C} (hX : isnt_colimity X) (hY : isnt_limity Y) (hX' : isExpanded X) (hY' : isExpanded Y) :
  syn2'_var_aux X Y → syn2'_var X Y

#eval Lean.versionString

mutual

inductive syn2' : (X Y : Obj d C) → Type
| var {X Y : Obj d C} : syn2'_var X Y → syn2' X Y
| id (X : String) : syn2' (Ovar X) (Ovar X)
| prod_mk {X Y Z : Obj d C} (f : syn2 X Y) (g : syn2 X Z) :
  syn2' X (prod Y Z)
| coprod_mk {X Y Z : Obj d C} (f : syn2 X Z) (g : syn2 Y Z) :
  syn2' (coprod X Y) Z
| extend {C D : Cat} {X : Obj d D} {Y : Obj d C} {F : FuncVar C D} (hF : F.hasLAdj d)
  (f : syn2 X (app F Y)) : syn2' (lAdjApp F hF X) Y
| restrict {C D : Cat} {X : Obj d C} {Y : Obj d D} {F : FuncVar C D} (hF : F.hasRAdj d)
  (f : syn2 (app F X) Y) : syn2' X (rAdjApp F hF Y)
| top_mk (X : Obj d C) : syn2' X top
| bot_mk (X : Obj d C) : syn2' bot X
| map {X Y : Obj d C} (F : FuncVar C D) (f : syn X Y) : syn2' (app F X) (app F Y)
| fst_comp {X Y Z : Obj d C} (f : syn2 X Z) : syn2' (prod X Y) Z
| snd_comp {X Y Z : Obj d C} (f : syn2 Y Z) : syn2' (prod X Y) Z
| comp_inl {X Y Z : Obj d C} (f : syn2 X Y) : syn2' X (coprod Y Z)
| comp_inr {X Y Z : Obj d C} (f : syn2 X Z) : syn2' X (coprod Y Z)
| comp_unit {X Y : Obj d D} (F : FuncVar C D) (hF : F.hasLAdj d) (f : syn2 X Y) :
  syn2' X (app F (lAdjApp F hF Y))
| counit_comp {X Y : Obj d D} (F : FuncVar C D) (hF : F.hasRAdj d) (f : syn2 X Y) :
  syn2' (app F (rAdjApp F hF X)) Y
deriving DecidableEq

inductive syn2 : (X Y : Obj d C) → Type
| of' : {X Y : Obj d C} → syn2' X Y → syn2 X Y
| comp' : {X Y Z : Obj d C} → syn2 X Y → syn2' Y Z → syn2 X Z

end

section decEq

mutual

def syn2'BEq : {X Y : Obj d C} → syn2' X Y → syn2' X Y → Bool
| _, _, syn2'.var f, syn2'.var g => decide (f = g)
| _, _, syn2'.id _, syn2'.id _ => true
| _, _, syn2'.prod_mk f₁ g₁, syn2'.prod_mk f₂ g₂ =>
  (syn2BEq f₁ f₂) && (syn2BEq g₁ g₂)
| _, _, syn2'.coprod_mk f₁ g₁, syn2'.coprod_mk f₂ g₂ =>
  (syn2BEq f₁ f₂) && (syn2BEq g₁ g₂)
| _, _, @syn2'.top_mk _ _, @syn2'.top_mk _ _ => true
| _, _, @syn2'.bot_mk _ _, @syn2'.bot_mk _ _ => true
| _, _, syn2'.fst_comp f, syn2'.fst_comp g => syn2BEq f g
| _, _, syn2'.snd_comp f, syn2'.snd_comp g => syn2BEq f g
| _, _, syn2'.comp_inl f, syn2'.comp_inl g => syn2BEq f g
| _, _, syn2'.comp_inr f, syn2'.comp_inr g => syn2BEq f g
| _, _, _, _ => false

def syn2BEq : {X Y : Obj d C} → syn2 X Y → syn2 X Y → Bool
| _, _, syn2.of' f, syn2.of' g => syn2'BEq f g
| _, _, @syn2.comp' _ _ Y₁ _ f₁ g₁, @syn2.comp' _ _ Y₂ _ f₂ g₂ =>
  if hY : Y₁ = Y₂
  then by subst hY; exact (syn2BEq f₁ f₂) && (syn2'BEq g₁ g₂)
  else false
| _, _, _, _ => false

end

axiom thing' {X Y : Obj d C}
  {f g : syn2' X Y} : syn2'BEq f g = true ↔ f = g

axiom thing {X Y : Obj d C}
  {f g : syn2 X Y} : syn2BEq f g = true ↔ f = g

instance {X Y : Obj d C} : DecidableEq (syn2' X Y) :=
λ f g : syn2' X Y =>
@decidable_of_decidable_of_iff (syn2'BEq f g = true) _ _ thing'

instance {X Y : Obj d C} : DecidableEq (syn2 X Y) :=
λ f g : syn2 X Y =>
@decidable_of_decidable_of_iff (syn2BEq f g = true) _ _ thing

end decEq

namespace syn2

def prod_mk {X Y Z : Obj d C}
  (f : syn2 X Y) (g : syn2 X Z) : syn2 X (prod Y Z) :=
syn2.of' (syn2'.prod_mk f g)

def coprod_mk {X Y Z : Obj d C}
  (f : syn2 X Z) (g : syn2 Y Z) : syn2 (coprod X Y) Z :=
syn2.of' (syn2'.coprod_mk f g)

def bot_mk (X : Obj d C) : syn2 bot X :=
syn2.of' (syn2'.bot_mk X)

def top_mk (X : Obj d C) : syn2 X top :=
syn2.of' (syn2'.top_mk X)

def fst_comp {X Y Z : Obj d C} (f : syn2 X Z) : syn2 (prod X Y) Z :=
syn2.of' (syn2'.fst_comp f)

def snd_comp {X Y Z : Obj d C} (f : syn2 Y Z) : syn2 (prod X Y) Z :=
syn2.of' (syn2'.snd_comp f)

def comp_inl {X Y Z : Obj d C} (f : syn2 X Y) : syn2 X (coprod Y Z) :=
syn2.of' (syn2'.comp_inl f)

def comp_inr {X Y Z : Obj d C} (f : syn2 X Z) : syn2 X (coprod Y Z) :=
syn2.of' (syn2'.comp_inr f)

def comp : {X Y Z : Obj d C} → syn2 X Y → syn2 Y Z → syn2 X Z
| _, _, _, f, syn2.of' g => syn2.comp' f g
| _, _, _, f, syn2.comp' g h => syn2.comp' (comp f g) h

def id : {X : Obj d C} → syn2 X X
| Ovar X => syn2.of' (syn2'.id X)
| prod _ _ => syn2.prod_mk (syn2.fst_comp id) (syn2.snd_comp id)
| coprod _ _ => syn2.coprod_mk (syn2.comp_inl id) (syn2.comp_inr id)
| top => top_mk _
| bot => bot_mk _

def fst {X Y : Obj d C} : syn2 (prod X Y) X :=
syn2.fst_comp syn2.id

def snd {X Y : Obj d C} : syn2 (prod X Y) Y :=
syn2.snd_comp syn2.id

def inl {X Y : Obj d C} : syn2 X (coprod X Y) :=
syn2.comp_inl syn2.id

def inr {X Y : Obj d C} : syn2 Y (coprod X Y) :=
syn2.comp_inr syn2.id

unsafe def of_syn2'_var_aux : {X Y : Obj d C} → syn2'_var_aux X Y → syn2 X Y
| Ovar _, Ovar _, v => syn2.of' $ syn2'.var (syn2'_var.Ovar_Ovar v)
| Ovar _, coprod _ _, v => syn2.of' $ syn2'.var $ syn2'_var.Ovar_coprod v
| Ovar _, bot, v => syn2.of' $ syn2'.var $ syn2'_var.Ovar_bot v
| prod _ _, Ovar _, v => syn2.of' $ syn2'.var $ syn2'_var.prod_Ovar v
| prod _ _, coprod _ _, v => syn2.of' $ syn2'.var $ syn2'_var.prod_coprod v
| prod _ _, bot, v => syn2.of' $ syn2'.var $ syn2'_var.prod_bot v
| top, Ovar _, v => syn2.of' $ syn2'.var $ syn2'_var.top_Ovar v
| top, coprod _ _, v => syn2.of' $ syn2'.var $ syn2'_var.top_coprod v
| top, bot, v => syn2.of' $ syn2'.var $ syn2'_var.top_bot v
| _, top, _ => top_mk _
| bot, _, _ => bot_mk _
| _, prod _ _, v => prod_mk (of_syn2'_var_aux v.comp_fst) (of_syn2'_var_aux v.comp_snd)
| coprod _ _, _, v => coprod_mk (of_syn2'_var_aux v.inl_comp) (of_syn2'_var_aux v.inr_comp)

unsafe def var {X Y : Obj d C} (f : String) : syn2 X Y :=
of_syn2'_var_aux (syn2'_var_aux.var f)

mutual

unsafe def cutelim_single :
  {X Y : Obj d C} → (f : syn2' X Y) →
  syn2' X Y × Bool -- Boolean indicates if any rewrites applied
| _, _, syn2'.prod_mk f g =>
  match cutelim f, cutelim g with
  | ⟨f, b₁⟩, ⟨g, b₂⟩ => ⟨syn2'.prod_mk f g, b₁ || b₂⟩
| _, _, syn2'.coprod_mk f g =>
  match cutelim f, cutelim g with
  | ⟨f, b₁⟩, ⟨g, b₂⟩ => ⟨syn2'.coprod_mk f g, b₁ || b₂⟩
| _, _, f => ⟨f, false⟩

/-- eliminates cuts from f ∘ g assuming f and g are both cut eliminated. -/
unsafe def cutelim_pair :
  {X Y Z : Obj d C} → (f : syn2' X Y) → (g : syn2' Y Z) →
  syn2 X Z × Bool -- Boolean indicates if any rewrites applied
| _, _, top, _, _ => ⟨syn2.top_mk _, true⟩
| bot, _, _, _, _ => ⟨syn2.bot_mk _, true⟩
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
| _, _, _, f, syn2'.comp_inl g => ((cutelim (syn2.comp (syn2.of' f) g)).1.comp_inl, true)
| _, _, _, f, syn2'.comp_inr g => ((cutelim (syn2.comp (syn2.of' f) g)).1.comp_inr, true)
| _, _, _, syn2'.fst_comp f, g => ((cutelim (syn2.comp' f g)).1.fst_comp, true)
| _, _, _, syn2'.snd_comp f, g => ((cutelim (syn2.comp' f g)).1.snd_comp, true)
| _, _, _, syn2'.id _, g => (syn2.of' g, true)
| _, _, _, f, syn2'.id _ => (syn2.of' f, true)
| _, _, _, f, g => ⟨syn2.comp' (syn2.of' f) g, false⟩

unsafe def cutelim :
  {X Y : Obj d C} → (f : syn2 X Y) → syn2 X Y × Bool
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

unsafe def normalize_single_ce :
  {X Y : Obj d C} → (f : syn2' X Y) → syn2 X Y × Bool
| coprod X Y, Z, syn2'.coprod_mk f g =>
  match X, Y, Z, normalize_ce f, normalize_ce g with
  | _, _, _, (@comp' _ _ _ Y₁ Z f₁ f₂, b₁), (@comp' _ _ _ Y₂ _ g₁ g₂, b₂) =>
    if h : Y₁ = Y₂
    then by
      subst h
      exact if f₂ = g₂
        then ((normalize_ce ((syn2.coprod_mk f₁ g₁).comp' f₂)).1, true)
        else (syn2.coprod_mk (comp' f₁ f₂) (comp' g₁ g₂), b₁ || b₂)
    else (syn2.coprod_mk (comp' f₁ f₂) (comp' g₁ g₂), b₁ || b₂)
  | _, _, _, (syn2.of' (syn2'.comp_inl f), _), (syn2.of' (syn2'.comp_inl g), _) =>
     ((normalize_ce (syn2.coprod_mk f g)).1.comp_inl, true)
   | _, _, _, (syn2.of' (syn2'.comp_inr f), _), (syn2.of' (syn2'.comp_inr g), _) =>
     ((normalize_ce (syn2.coprod_mk f g)).1.comp_inr, true)
  | _, _, _, (syn2.of' (syn2'.prod_mk f g), _), (syn2.of' (syn2'.prod_mk h i), _) =>
    (syn2.prod_mk (normalize_ce (syn2.coprod_mk f h)).1 (normalize_ce (syn2.coprod_mk g i)).1, true)
  | _, _, _, (f, b₁), (g, b₂) => (syn2.coprod_mk f g, b₁ || b₂)
| _, _, syn2'.fst_comp f =>
  match normalize_ce f with
  | (syn2.of' (syn2'.prod_mk f g), _) => (syn2.prod_mk (syn2.fst_comp f) (syn2.fst_comp g), true)
  | (syn2.of' (syn2'.comp_inl f), _) => (syn2.comp_inl (syn2.fst_comp f), true)
  | (syn2.of' (syn2'.comp_inr f), _) => (syn2.comp_inr (syn2.fst_comp f), true)
  | (e, b) => (e.fst_comp, b)
| _, _, syn2'.snd_comp f =>
  match normalize_ce f with
  | (syn2.of' (syn2'.prod_mk f g), _) => (syn2.prod_mk (syn2.snd_comp f) (syn2.snd_comp g), true)
  | (syn2.of' (syn2'.comp_inl f), _) => (syn2.comp_inl (syn2.snd_comp f), true)
  | (syn2.of' (syn2'.comp_inr f), _) => (syn2.comp_inr (syn2.snd_comp f), true)
  | (e, b) => (e.snd_comp, b)
| _, _, syn2'.comp_inl f =>
  match normalize_ce f with
  | (f, b) => (f.comp_inl, b)
| _, _, syn2'.comp_inr f =>
  match normalize_ce f with
  | (f, b) => (f.comp_inr, b)
| _, _, syn2'.prod_mk f g =>
  match normalize_ce f, normalize_ce g with
  | (f, false), (g, false) => (syn2.prod_mk f g, false)
  | (f, _), (g, _) => (syn2.prod_mk f g, true)
| _, _, f => (syn2.of' f, false)

/-- Normalizes a pair assuming both parts of the pair are normalized -/
unsafe def normalize_pair_ce :
  {X Y Z : Obj d C} → (f : syn2' X Y) →
  (g : syn2' Y Z) → syn2 X Z × Bool
| _, _, _, f, syn2'.prod_mk g h =>
  ⟨syn2.prod_mk (normalize_ce ((syn2.of' f).comp g)).1 (normalize_ce ((syn2.of' f).comp h)).1, true⟩
| _, _, _, f, syn2'.comp_inl g => ((normalize_ce (syn2.comp (syn2.of' f) g)).1.comp_inl, true)
| _, _, _, f, syn2'.comp_inr g => ((normalize_ce (syn2.comp (syn2.of' f) g)).1.comp_inr, true)
| _, _, _, syn2'.fst_comp f, g => ((normalize_ce (syn2.comp' f g)).1.fst_comp, true)
| _, _, _, syn2'.snd_comp f, g => ((normalize_ce (syn2.comp' f g)).1.snd_comp, true)
| _, _, _, f, g => ⟨syn2.comp' (syn2.of' f) g, false⟩

unsafe def normalize_ce :
  {X Y : Obj d C} → (f : syn2 X Y) → syn2 X Y × Bool
| _, _, syn2.of' f => normalize_single_ce f
| _, _, syn2.comp' f g =>
  match normalize_single_ce g with
  | (syn2.of' g, b₁) =>
    match normalize_ce f with
    | (syn2.of' f, b₂) =>
      let n := normalize_pair_ce f g
      (n.1, b₁ || b₂ || n.2)
    | (syn2.comp' e f, b₂) =>
      match normalize_pair_ce f g with
      | ⟨fg, true⟩ => let n := normalize_ce (e.comp fg)
        (n.1, b₁ || b₂ || n.2)
      | ⟨fg, false⟩ => (e.comp fg, b₁ || b₂)
  | (g, _) => ((normalize_ce (f.comp g)).1, true)

end

unsafe def normalize
  {X Y : Obj d C} (s : syn2 X Y) : syn2 X Y :=
(normalize_ce (cutelim s).1).1

unsafe def of_syn : {X Y : Obj d C} → (f : syn X Y) → syn2 X Y
| _, _, syn.var f => syn2.var f
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

unsafe def beq {X Y : Obj d C} (f g : syn X Y) : Bool :=
decide (syn2.normalize (syn2.of_syn f) = syn2.normalize (syn2.of_syn g))

end syn