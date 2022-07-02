
inductive Cat :=
| Set : Cat
| var (n : Nat) : Cat

open Sum

mutual

inductive Obj : Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| corepr {C : Cat} (F : Func C Cat.Set) : Obj C
| app' {C D : Cat} (F : Func' C D) (X : Obj C) : Obj D

inductive Func' : (C : Cat) → Cat → Type where
| var (C D : Cat) (n : Nat) : Func' C D
| hom (C : Cat) (X : Obj C) : Func' C Cat.Set -- X is the domain
| prod {C : Cat} (F G : Func C Cat.Set) : Func' C Cat.Set

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| comp' {C D E : Cat} (F : Func' C D) (G : Func D E) : Func C E

end

-- def Func.comp : {C D E : Cat} → (F : Func C D) → (G : Func D E) → Func C E
-- | _, _, _, Func.id _,      G => G
-- | _, _, _, Func.comp' F G, H => Func.comp' F (comp G H)
-- #print prefix Func
noncomputable def Func.comp {C D : Cat} (F : Func C D) : (E : Cat) → (G : Func D E) → Func C E :=
@Func.recOn (λ _ _ => Unit) (λ C D _ => Unit) (λ C D F => (E : Cat) → (G : Func D E) → Func C E)
  C
  D
  F
  (λ _ _ => ())
  (λ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ C' D' G => G)
  (λ F _ _ ih E' G => Func.comp' F (ih _ G))

-- def Func.app : {C D : Cat} → (F : Func C D) → Obj C → Obj D
-- | _, _, Func.id _,      X => X
-- | _, _, Func.comp' F G, X => app G (Obj.app' F X)

noncomputable def Func.app {C D : Cat} (F : Func C D) : (X : Obj C) → Obj D :=
@Func.recOn (λ _ _ => Unit) (λ C D _ => Unit) (λ C D _ => Obj C → Obj D)
  C
  D
  F
  (λ _ _ => ())
  (λ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ X => X)
  (λ F _ _ ih X => ih (Obj.app' F X))

theorem appInj {C₁ C₂ D : Cat} {F₁ : Func C₁ D} {F₂ : Func C₂ D}
  {X₁ : Obj C₁} {X₂ : Obj C₂}
  (h : F₁.app X₁ = F₂.app X₂) :
  C₁ = C₂ ∧ HEq F₁ F₂ ∧ HEq X₁ X₂ := sorry

--   by
-- cases F₁
-- . cases F₂
--   . cases X₁
--     . cases X₂
--       . injection h with _ n_eq
--         subst n_eq
--         exact ⟨rfl, rfl⟩
--       . injection h
--     . cases X₂
--       . injection h
--       . injection h with _ F_eq
--         subst F_eq
--         exact ⟨rfl, rfl⟩
--   . cases X₁
--     . cases X₂
--       . rw [Func.app, Func.app] at h
--         simp at h
--         injection h




@[reducible] def Func.hom {C : Cat} (X : Obj C) : Func C Cat.Set :=
Func.comp' (Func'.hom C X) (Func.id _)

def Func.var (C D : Cat) (n : Nat) : Func C D :=
Func.comp' (Func'.var C D n) (Func.id _)

def Func.prod {C : Cat} (F G : Func C Cat.Set) : Func C Cat.Set :=
Func.comp' (Func'.prod F G) (Func.id _)

@[reducible] def homm {C : Cat} (X Y : Obj C) : Obj Cat.Set :=
Obj.app' (Func'.hom C X) Y

theorem hommEqHom {C : Cat} (X Y : Obj C) : homm X Y = (Func.hom X).app Y := rfl

open Func Obj

structure Context : Type 1 :=
(elem : Obj Cat.Set → Type)
(isCorepr : {C : Cat} → Func C Set → Prop)

variable (Γ : Context)

inductive Elem : (X : Obj Cat.Set) → Type
| var (X : Obj Cat.Set) (x : Γ.elem X) : Elem X
| id {C : Cat} (X : Obj C) : Elem ((hom X).app X)
| comp {C : Cat} {X Y Z : Obj C}
  (f : Elem ((hom X).app Y))
  (g : Elem ((hom Y).app Z)) : Elem ((hom X).app Z)
| app {X Y : Obj Cat.Set} (f : Elem ((hom X).app Y)) (x : Elem X) : Elem Y
| map {C D : Cat} (F : Func C D) {X Y : Obj C} (f : Elem ((hom X).app Y)) :
  Elem (app (hom (app F X)) (app F Y))
| extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
  Elem ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) :
  Elem (app F (corepr F))
| prodMk {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : Elem (F.app X)) (y : Elem (G.app X)) :
  Elem ((F.prod G).app X)
| prodFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : Elem ((F.prod G).app X)) : Elem (F.app X)
| prodSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x : Elem ((F.prod G).app X)) : Elem (G.app X)

inductive Rel : {X : Obj Cat.Set} → (x y : Elem Γ X) → Prop
| refl {X : Obj Cat.Set} (x : Elem Γ X) : Rel x x
| symm {X : Obj Cat.Set} {x y : Elem Γ X} : Rel x y → Rel y x
| trans {X : Obj Cat.Set} {x y z : Elem Γ X} : Rel x y → Rel y z → Rel x z
| idComp {C : Cat} {X Y : Obj C} {f : Elem Γ ((hom X).app Y)} :
  Rel ((Elem.id X).comp f) f
| compId {C : Cat} {X Y : Obj C} {f : Elem Γ ((hom X).app Y)} :
  Rel (f.comp (Elem.id Y)) f
| compAssoc {C : Cat} {W X Y Z : Obj C} (f : Elem Γ ((hom W).app X))
  (g : Elem Γ ((hom X).app Y)) (h : Elem Γ ((hom Y).app Z)) :
  Rel ((f.comp g).comp h) (f.comp (g.comp h))
| idApp {X : Obj Cat.Set} (x : Elem Γ X) :
  Rel ((Elem.id X).app x) x
| compApp {X Y Z : Obj Cat.Set} (f : Elem Γ ((hom X).app Y))
  (g : Elem Γ ((hom Y).app Z)) (x : Elem Γ X):
  Rel ((f.comp g).app x) (g.app (f.app x))
| mapId {C D : Cat} (F : Func C D) (X : Obj C) :
  Rel (Elem.map F (Elem.id X)) (Elem.id (F.app X))
| mapComp {C D : Cat} (F : Func C D) {X Y Z : Obj C}
  (f : Elem Γ ((hom X).app Y)) (g : Elem Γ ((hom Y).app Z)) :
  Rel (Elem.map F (f.comp g)) ((Elem.map F f).comp (Elem.map F g))
| fstMk {C : Cat} (F G : Func C Cat.Set){X : Obj C}
  (x : Elem Γ (F.app X)) (y : Elem Γ (G.app X)) :
  Rel (Elem.prodFst (x.prodMk y)) x
| sndMk {C : Cat} (F G : Func C Cat.Set){X : Obj C}
  (x : Elem Γ (F.app X)) (y : Elem Γ (G.app X)) :
  Rel (Elem.prodSnd (x.prodMk y)) y
| compCongr {C : Cat} {X Y Z : Obj Cat.Set} {f₁ f₂ : Elem Γ ((hom X).app Y)}
  {g₁ g₂ : Elem Γ ((hom Y).app Z)} :
  Rel f₁ f₂ → Rel g₁ g₂ → Rel (f₁.comp g₁) (f₂.comp g₂)
| appCongr {X Y : Obj Cat.Set} {f₁ f₂ : Elem Γ ((hom X).app Y)} {x₁ x₂ : Elem Γ X} :
  Rel f₁ f₂ → Rel x₁ x₂ → Rel (f₁.app x₁) (f₂.app x₂)
| mapCongr {C D : Cat} {F : Func C D} {X Y : Obj C} {f₁ f₂ : Elem Γ ((hom X).app Y)} :
  Rel f₁ f₂ → Rel (Elem.map F f₁) (Elem.map F f₂)
| prodMkCongr {C : Cat} (F G : Func C Cat.Set) {X : Obj C}
  {x₁ x₂ : Elem Γ (F.app X)} {y₁ y₂ : Elem Γ (G.app X)} :
  Rel x₁ x₂ → Rel y₁ y₂ → Rel (x₁.prodMk y₁) (x₂.prodMk y₂)
| prodFstCongr {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x₁ x₂ : Elem Γ ((F.prod G).app X)) :
  Rel x₁ x₂ → Rel x₁.prodFst x₂.prodFst
| prodSndCongr {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
  (x₁ x₂ : Elem Γ ((F.prod G).app X)) :
  Rel x₁ x₂ → Rel x₁.prodSnd x₂.prodSnd

inductive HeadSymbol
| VEU : HeadSymbol -- var, extend or unit
| Fst : HeadSymbol
| Snd : HeadSymbol
| ProdMk : HeadSymbol
| IC : HeadSymbol -- id, comp
| AM : HeadSymbol -- app, map

open HeadSymbol
-- Don't need composition. hom is already a functor.
inductive NormElemAux : HeadSymbol → Obj Cat.Set → Type
| var {X : Obj Cat.Set} (x : Γ.elem X) : NormElemAux VEU X
| id {C : Cat} (X : Obj C) : NormElemAux ICAM ((Func.hom X).app X)
| comp {C : Cat} {X Y Z : Obj C} {s t : HeadSymbol} (hs : s ≠ IC)
  (f : NormElemAux s ((hom X).app Y))
  (g : NormElemAux t ((hom Y).app Z)) : NormElemAux IC ((hom X).app Z)
| app {X Y : Obj Cat.Set} {s t : HeadSymbol} (hs : s ≠ IC) (f : NormElemAux s ((hom X).app Y))
  (x : NormElemAux t X) : NormElemAux AM Y
| map {C D : Cat} (F : Func C D) --shold be Func'
  {X Y : Obj C} {s : HeadSymbol} (hs : s ≠ IC)
  (f : NormElemAux s ((hom X).app Y)) :
  NormElemAux AM (app (hom (app F X)) (app F Y))
| extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
  NormElemAux VEU ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : Cat} (F : Func C Cat.Set)  (h : Γ.isCorepr F) :
  NormElemAux VEU (app F (corepr F))
| prodMk {C : Cat} {F G : Func C Cat.Set} {X : Obj C} {s t : HeadSymbol}
  (hst : s ≠ Fst ∨ t ≠ Snd)
  (x : NormElemAux s (F.app X)) (y : NormElemAux t (G.app X)) :
  NormElemAux ProdMk ((F.prod G).app X)
| prodFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C} {s : HeadSymbol}
  (hs : s ≠ ProdMk)
  (x : NormElemAux s ((F.prod G).app X)) : NormElemAux Fst (F.app X)
| prodSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C} {s : HeadSymbol}
  (hs : s ≠ ProdMk)
  (x : NormElemAux s ((F.prod G).app X)) : NormElemAux Snd (G.app X)

def NormElem (X : Obj Cat.Set) : Type :=
(s : HeadSymbol) × NormElemAux Γ s X

/- Suppose I do reprs at the same time. -/

namespace NormElem

variable {C : Cat}
variable {Γ}

def var (X : Obj Cat.Set) (v : Γ.elem X) : NormElem Γ X :=
⟨VEU, NormElemAux.var v⟩

def id (X : Obj C) : NormElem Γ ((hom X).app X) :=
⟨IC, NormElemAux.id X⟩

noncomputable def compAux
  {A : Obj Cat.Set}
  {s : HeadSymbol}
  (f : NormElemAux Γ s A) :
  {X Y Z : Obj C} →
  (hA : A = ((hom X).app Y)) →
  {B : Obj Cat.Set} →
  (hB : B = ((hom Y).app Z)) →
  {t : HeadSymbol} →
  (g : NormElemAux Γ t B) →
  NormElem Γ ((hom X).app Z) :=
@NormElemAux.recOn Γ
  (λ s A f => (X Y Z : Obj C) → (hA : A = ((hom X).app Y)) →
    (B : Obj Cat.Set) →
    (hB : B = ((hom Y).app Z)) →
    (t : HeadSymbol) →
    (g : NormElemAux Γ t B) →
    NormElem Γ ((hom X).app Z))
  s A f
  (λ f' X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    subst hA hB
    exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion
      (NormElemAux.var f') g⟩)
  (λ A' X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    subst hB
    injection hA with C_eq _ F_eq A_eq
    subst C_eq
    have F_eq' := eq_of_heq F_eq
    injection F_eq' with F_eq₂ A_eq₂
    subst A_eq₂
    have A_eq' := eq_of_heq A_eq
    subst A_eq'
    exact ⟨_, g⟩)
  (λ hs f' g' ihf ihg X Y Z hA B hB _ h' => show NormElem Γ (app (hom X) Z) by
    subst hB
    injection hA with C_eq _ F_eq A_eq
    subst C_eq
    have F_eq' := eq_of_heq F_eq
    injection F_eq' with F_eq₂ A_eq₂
    subst A_eq₂
    have A_eq' := eq_of_heq A_eq
    subst A_eq'
    exact ⟨_, NormElemAux.comp hs f' (ihg _ _ _ rfl _ rfl _ h').2⟩)
  (λ hs f' x ihf ihx X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
      subst hB hA
      exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.app hs f' x) g⟩)
  (λ F X Y s hs f' ihf Z V W hA B hB t g => show NormElem Γ (app (hom Z) W) by
    subst hB
    injection hA with C_eq _ F_eq A_eq
    subst C_eq
    have F_eq' := eq_of_heq F_eq
    injection F_eq' with F_eq₂ A_eq₂
    subst A_eq₂
    have A_eq' := eq_of_heq A_eq
    subst A_eq'
    exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.map F hs f') g⟩)
  (λ F hC W  X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    subst hB
    injection hA with C_eq _ F_eq A_eq
    subst C_eq
    have F_eq' := eq_of_heq F_eq
    injection F_eq' with F_eq₂ A_eq₂
    subst A_eq₂
    have A_eq' := eq_of_heq A_eq
    subst A_eq'
    exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.extend _ hC) g⟩)
  (λ F hC X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    subst hB
    have hA₁ := (appInj hA).1
    subst hA₁
    have hA₂ := eq_of_heq (appInj hA).2.1
    subst hA₂
    have hA₃ := eq_of_heq (appInj hA).2.2
    subst hA₃
    exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.unit _ hC) g⟩)
  (λ hst f₁ f₂ ih₁ ih₂ X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    injection hA with C_eq _ F_eq
    subst C_eq
    have F_eq' := eq_of_heq F_eq
    injection F_eq')
  (λ hs f' ih X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    subst hB
    have hA₁ := (appInj hA).1
    subst hA₁
    have hA₂ := eq_of_heq (appInj hA).2.1
    subst hA₂
    have hA₃ := eq_of_heq (appInj hA).2.2
    subst hA₃
    exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.prodFst hs f') g⟩)
  (λ hs f' ih X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
    subst hB
    have hA₁ := (appInj hA).1
    subst hA₁
    have hA₂ := eq_of_heq (appInj hA).2.1
    subst hA₂
    have hA₃ := eq_of_heq (appInj hA).2.2
    subst hA₃
    exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.prodSnd hs f') g⟩)

noncomputable def comp {X Y Z : Obj C}
  (f : NormElem Γ ((hom X).app Y))
  (g : NormElem Γ ((hom Y).app Z)) :
  NormElem Γ ((hom X).app Z) :=
compAux f.2 rfl rfl g.2

end NormElem

-- mutual



-- -- prodMk can only be applied to terms not of the form fst snd.

-- -- We have raw Elems and Elems. Elems are the closure under identity
-- -- and composition functor map and function application of raw Elems.
-- -- We can only apply or map raw homs.

-- inductive RawElem : Obj Cat.Set → Type where
-- | var (X : Obj Cat.Set) (x : Γ.elem X) : RawElem X
-- | extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
--   RawElem ((app (hom (app F X)) (app (hom (corepr F)) X)))
-- | unit {C : Cat} (F : Func C Cat.Set)  (h : Γ.isCorepr F) :
--   RawElem (app F (corepr F))

-- inductive RawElemFst : Obj Cat.Set → Type where
-- | ofVar {C : Cat} {F G : Func C Cat.Set} {X : Obj C} (x : Γ.elem ((F.prod G).app X)) :
--   RawElemFst (F.app X)
-- | ofRawElemSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemSnd ((F.prod G).app X)) : RawElemFst (F.app X)
-- | ofCompMapAppElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : CompMapAppElem ((F.prod G).app X)) : RawElemFst (F.app X)

-- inductive RawElemSnd : Obj Cat.Set → Type where
-- | ofVar {C : Cat} {F G : Func C Cat.Set} {X : Obj C} (x : Γ.elem ((F.prod G).app X)) :
--   RawElemSnd (G.app X)
-- | ofRawElemFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemFst ((F.prod G).app X)) : RawElemSnd (G.app X)
-- | ofCompMapAppElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : CompMapAppElem ((F.prod G).app X)) : RawElemFst (G.app X)

-- inductive RawElemProdMk : Obj Cat.Set → Type where
-- | ofRawElemRawElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElem (F.app X)) (y : RawElem (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemRawElemFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElem (F.app X)) (y : RawElemFst (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemRawElemSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElem (F.app X)) (y : RawElemSnd (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemRawElemProdMk {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElem (F.app X)) (y : RawElemProdMk (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElem (F.app X)) (y : Elem (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)

-- | ofRawElemFstRawElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemFst (F.app X)) (y : RawElem (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemFstRawElemFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemFst (F.app X)) (y : RawElemFst (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemFstRawElemProdMk {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemFst (F.app X)) (y : RawElemProdMk (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemFstElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemFst (F.app X)) (y : Elem (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)

-- | ofRawElemSndRawElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemSnd (F.app X)) (y : RawElem (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemRawElemFst {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemSnd (F.app X)) (y : RawElemFst (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemRawElemSnd {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemSnd (F.app X)) (y : RawElemSnd (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemRawElemProdMk {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemSnd (F.app X)) (y : RawElemProdMk (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)
-- | ofRawElemElem {C : Cat} {F G : Func C Cat.Set} {X : Obj C}
--   (x : RawElemSnd (F.app X)) (y : Elem (G.app X)) :
--   RawElemProdMk ((F.prod G).app X)

-- inductive CompMapAppElem : Obj Cat.Set → Type where
-- | id {C : Cat} (X : Obj C) : Elem ((Func.hom X).app X)
-- |

-- end

-- end NormElem