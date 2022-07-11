inductive Cat :=
| Set : Cat
| var (n : Nat) : Cat

open Sum

mutual

inductive Obj : Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| corepr {C : Cat} (F : Func C Cat.Set) : Obj C
| app' {C D : Cat} (v : Nat) (X : Obj C) : Obj D
| prod (X Y : Obj Cat.Set) : Obj Cat.Set
| hom {C : Cat} (X Y : Obj C) : Obj Cat.Set

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| compVar {C D E : Cat} (F : Func C D) (v : Nat) : Func C E
| prod {C : Cat} (F G : Func C Cat.Set) : Func C Cat.Set
| hom (C : Cat) (X : Obj C) : Func C Cat.Set
| compHom {C D : Cat} (F : Func C D) (X : Obj D) : Func C Cat.Set

end

mutual

def ObjContainsCorepr : {D : Cat} → (F : Func D Cat.Set) → {C : Cat} → Obj C → Prop
| _, F, _, Obj.var _ _  => False
| _, F, _, Obj.corepr G => FuncContainsCorepr F G ∨ HEq F G
| _, F, _, Obj.app' _ X => ObjContainsCorepr F X
| _, F, _, Obj.prod X Y => ObjContainsCorepr F X ∨ ObjContainsCorepr F Y
| _, F, _, Obj.hom X Y => ObjContainsCorepr F X ∨ ObjContainsCorepr F Y

def FuncContainsCorepr : {C : Cat} → (F : Func C Cat.Set) → {C' D' : Cat} → (G : Func C' D') → Prop
| _, F, _, _, Func.id _        => False
| _, F, _, _, Func.compVar G _ => FuncContainsCorepr F G
| _, F, _, _, Func.prod G₁ G₂  => FuncContainsCorepr F G₁ ∨ FuncContainsCorepr F G₂
| _, F, _, _, Func.hom _ X     => ObjContainsCorepr F X
| _, F, _, _, Func.compHom G X => FuncContainsCorepr F G ∨ ObjContainsCorepr F X

end

noncomputable def Func.compAux {D E : Cat} (G : Func D E) : (C : Cat) → (F : Func C D) → Func C E :=
@Func.recOn (λ _ _ => Unit) (λ D E G => (C : Cat) → (F : Func C D) → Func C E)
  D E G
  (λ _ _ => ())
  (λ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ G => G)
  (λ G v ih C F => Func.compVar (ih _ F) v)
  (λ G₁ G₂ ih₁ ih₂ C F => Func.prod (ih₁ _ F) (ih₂ _ F))
  (λ D X _ C F => Func.compHom F X)
  (λ G X ih _ C G => Func.compHom (ih _ G) X)

noncomputable def Func.app {C D : Cat} (F : Func C D) : (X : Obj C) → Obj D :=
@Func.recOn (λ _ _ => Unit) (λ C D _ => Obj C → Obj D)
  C D F
  (λ _ _ => ())
  (λ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ X => X)
  (λ F v ih X => Obj.app' v (ih X))
  (λ F₁ F₂ ih₁ ih₂ X => Obj.prod (ih₁ X) (ih₂ X))
  (λ C Y  _ X => Obj.hom Y X)
  (λ F Y ih _ X => Obj.hom Y (ih X))

def Func.var (C D : Cat) (v : Nat) : Func C D :=
Func.compVar (Func.id _) v

open Func Obj

structure Context : Type 1 :=
( elem : Obj Cat.Set → Type )
( isCorepr : {C : Cat} → Func C Set → Prop )

variable (Γ : Context)

inductive Elem : (X : Obj Cat.Set) → Type
| var (X : Obj Cat.Set) (x : Γ.elem X) : Elem X
| id {C : Cat} (X : Obj C) : Elem (hom X X)
| comp {C : Cat} {X Y Z : Obj C}
  (f : Elem (hom X Y))
  (g : Elem (hom Y Z)) : Elem (hom X Z)
| app {X Y : Obj Cat.Set} (f : Elem (hom X Y)) (x : Elem X) : Elem Y
| map {C D : Cat} (F : Func C D) {X Y : Obj C} (f : Elem (hom X Y)) :
  Elem (hom (F.app X) (F.app Y))
| extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
  Elem ((hom (app F X) (hom (corepr F) X)))
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
| idComp {C : Cat} {X Y : Obj C} {f : Elem Γ (hom X Y)} :
  Rel ((Elem.id X).comp f) f
| compId {C : Cat} {X Y : Obj C} {f : Elem Γ (hom X Y)} :
  Rel (f.comp (Elem.id Y)) f
| compAssoc {C : Cat} {W X Y Z : Obj C} (f : Elem Γ (hom W X))
  (g : Elem Γ (hom X Y)) (h : Elem Γ (hom Y Z)) :
  Rel ((f.comp g).comp h) (f.comp (g.comp h))
| idApp {X : Obj Cat.Set} (x : Elem Γ X) :
  Rel ((Elem.id X).app x) x
| compApp {X Y Z : Obj Cat.Set} (f : Elem Γ (hom X Y))
  (g : Elem Γ (hom Y Z)) (x : Elem Γ X):
  Rel ((f.comp g).app x) (g.app (f.app x))
| mapId {C D : Cat} (F : Func C D) (X : Obj C) :
  Rel (Elem.map F (Elem.id X)) (Elem.id (F.app X))
| mapComp {C D : Cat} (F : Func C D) {X Y Z : Obj C}
  (f : Elem Γ (hom X Y)) (g : Elem Γ (hom Y Z)) :
  Rel (Elem.map F (f.comp g)) ((Elem.map F f).comp (Elem.map F g))
| fstMk {C : Cat} (F G : Func C Cat.Set) {X : Obj C}
  (x : Elem Γ (F.app X)) (y : Elem Γ (G.app X)) :
  Rel (Elem.prodFst (x.prodMk y)) x
| sndMk {C : Cat} (F G : Func C Cat.Set) {X : Obj C}
  (x : Elem Γ (F.app X)) (y : Elem Γ (G.app X)) :
  Rel (Elem.prodSnd (x.prodMk y)) y
| compCongr {C : Cat} {X Y Z : Obj Cat.Set} {f₁ f₂ : Elem Γ (hom X Y)}
  {g₁ g₂ : Elem Γ (hom Y Z)} :
  Rel f₁ f₂ → Rel g₁ g₂ → Rel (f₁.comp g₁) (f₂.comp g₂)
| appCongr {X Y : Obj Cat.Set} {f₁ f₂ : Elem Γ (hom X Y)} {x₁ x₂ : Elem Γ X} :
  Rel f₁ f₂ → Rel x₁ x₂ → Rel (f₁.app x₁) (f₂.app x₂)
| mapCongr {C D : Cat} {F : Func C D} {X Y : Obj C} {f₁ f₂ : Elem Γ (hom X Y)} :
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
| veu : HeadSymbol -- var, extend or unit
| fst : HeadSymbol
| snd : HeadSymbol
| prodMk : HeadSymbol
| ic : HeadSymbol -- id, comp
| ma : HeadSymbol --map, app

/-
  Normalisation rules.
  -- Cannot double apply, all applications have to be a of the form (f ∘ g) x and not f (g x)
  -- Cannot apply prodMk to pairs of Fst and Snd
  -- Cannot apply Fst or Snd to ProdMk
  -- The left part of a composition cannot be id or a composition. The right part must be.
  -- Functor maps can only be done with functor variables
  -- Cannot map the identity function with a functor.
  -- Cannot compose two functor maps of the same functor. F (f ∘ g) is preferred over F (f) ∘ F (g)
-/

/-
  More Abstract Way.
  -- Suppose we have f : X → Y where X and Y are Objects of C
  -- If X is corepr, then f must be either extend or a variable to be almostNormal
  -- If X is not corepr then it is normal if it is blah blah blah context.
-/

open HeadSymbol
-- Don't need composition. hom is already a functor.
inductive NormElemAux : HeadSymbol → Obj Cat.Set → Type
| var {X : Obj Cat.Set} (x : Γ.elem X) : NormElemAux veu X
| id {C : Cat} (X : Obj C) : NormElemAux ic (hom X X)
| comp {C : Cat} {X Y Z : Obj C} {s : HeadSymbol} (hs : s ≠ ic)
  (f : NormElemAux s (hom X Y)) (g : NormElemAux ic (hom Y Z)) :
  NormElemAux ic (hom X Z)
| app {X Y : Obj Cat.Set} {s t : HeadSymbol} (hs : s ≠ ic)
  (f : NormElemAux s (hom X Y))
  (x : NormElemAux t X) : NormElemAux ma Y
| map {C D : Cat} (v : Nat)
  {X Y : Obj C} {s : HeadSymbol} (hs : s ≠ ic) :
  (f : NormElemAux s (hom X Y)) →
  NormElemAux ma (hom ((Func.var C D v).app X) ((Func.var C D v).app Y))
| extend {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) {X : Obj C} :
  NormElemAux veu ((hom (app F X) (hom (corepr F) X)))
| unit {C : Cat} (F : Func C Cat.Set) (h : Γ.isCorepr F) :
  NormElemAux veu (app F (corepr F))
| prodMk {X Y : Obj Cat.Set} {s t : HeadSymbol}
  (hst : s ≠ fst ∨ t ≠ snd)
  (x : NormElemAux s X) (y : NormElemAux t Y) :
  NormElemAux prodMk (X.prod Y)
| prodFst {X Y : Obj Cat.Set} {s : HeadSymbol}
  (hs : s ≠ prodMk)
  (x : NormElemAux s (X.prod Y)) : NormElemAux fst X
| prodSnd {X Y : Obj Cat.Set} {s : HeadSymbol}
  (hs : s ≠ prodMk)
  (x : NormElemAux s (X.prod Y)) : NormElemAux snd Y

def NormElem (X : Obj Cat.Set) : Type :=
(s : HeadSymbol) × NormElemAux Γ s X

/- Suppose I do reprs at the same time. -/

namespace NormElem

variable {C : Cat}
variable {Γ}

def var (X : Obj Cat.Set) (v : Γ.elem X) : NormElem Γ X :=
⟨veu, NormElemAux.var v⟩

def id (X : Obj C) : NormElem Γ (hom X X) :=
⟨_, NormElemAux.id X⟩

def comp : {C : Cat} → {X Y Z : Obj C} →
  (f : NormElem Γ (hom X Y)) →
  (g : NormElem Γ (hom Y Z)) →
  NormElem Γ (hom X Z)
| _, _, _,


-- noncomputable def compAux
--   {A : Obj Cat.Set}
--   {s : HeadSymbol}
--   (f : NormElemAux Γ s A) :
--   {X Y Z : Obj C} →
--   (hA : A = (hom X Y)) →
--   {B : Obj Cat.Set} →
--   (hB : B = (hom Y Z)) →
--   {t : HeadSymbol} →
--   (g : NormElemAux Γ t B) →
--   NormElem Γ (hom X Z) :=
-- @NormElemAux.recOn Γ
--   (λ s A f => (X Y Z : Obj C) → (hA : A = (hom X Y)) →
--     (B : Obj Cat.Set) →
--     (hB : B = (hom Y Z)) →
--     (t : HeadSymbol) →
--     (g : NormElemAux Γ t B) →
--     NormElem Γ (hom X Z))
--   s A f
--   (λ f' X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     subst hA hB
--     exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion
--       (NormElemAux.var f') g⟩)
--   (λ A' X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     subst hB
--     injection hA with C_eq _ F_eq A_eq
--     subst C_eq
--     have F_eq' := eq_of_heq F_eq
--     injection F_eq' with F_eq₂ A_eq₂
--     subst A_eq₂
--     have A_eq' := eq_of_heq A_eq
--     subst A_eq'
--     exact ⟨_, g⟩)
--   (λ hs f' g' ihf ihg X Y Z hA B hB _ h' => show NormElem Γ (app (hom X) Z) by
--     subst hB
--     injection hA with C_eq _ F_eq A_eq
--     subst C_eq
--     have F_eq' := eq_of_heq F_eq
--     injection F_eq' with F_eq₂ A_eq₂
--     subst A_eq₂
--     have A_eq' := eq_of_heq A_eq
--     subst A_eq'
--     exact ⟨_, NormElemAux.comp hs f' (ihg _ _ _ rfl _ rfl _ h').2⟩)
--   (λ hs f' x ihf ihx X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--       subst hB hA
--       exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.app hs f' x) g⟩)
--   (λ F X Y s hs f' ihf Z V W hA B hB t g => show NormElem Γ (app (hom Z) W) by
--     subst hB
--     injection hA with C_eq _ F_eq A_eq
--     subst C_eq
--     have F_eq' := eq_of_heq F_eq
--     injection F_eq' with F_eq₂ A_eq₂
--     subst A_eq₂
--     have A_eq' := eq_of_heq A_eq
--     subst A_eq'
--     exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.map F hs f') g⟩)
--   (λ F hC W  X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     subst hB
--     injection hA with C_eq _ F_eq A_eq
--     subst C_eq
--     have F_eq' := eq_of_heq F_eq
--     injection F_eq' with F_eq₂ A_eq₂
--     subst A_eq₂
--     have A_eq' := eq_of_heq A_eq
--     subst A_eq'
--     exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.extend _ hC) g⟩)
--   (λ F hC X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     subst hB
--     have hA₁ := (appInj hA).1
--     subst hA₁
--     have hA₂ := eq_of_heq (appInj hA).2.1
--     subst hA₂
--     have hA₃ := eq_of_heq (appInj hA).2.2
--     subst hA₃
--     exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.unit _ hC) g⟩)
--   (λ hst f₁ f₂ ih₁ ih₂ X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     injection hA with C_eq _ F_eq
--     subst C_eq
--     have F_eq' := eq_of_heq F_eq
--     injection F_eq')
--   (λ hs f' ih X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     subst hB
--     have hA₁ := (appInj hA).1
--     subst hA₁
--     have hA₂ := eq_of_heq (appInj hA).2.1
--     subst hA₂
--     have hA₃ := eq_of_heq (appInj hA).2.2
--     subst hA₃
--     exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.prodFst hs f') g⟩)
--   (λ hs f' ih X Y Z hA B hB t g => show NormElem Γ (app (hom X) Z) by
--     subst hB
--     have hA₁ := (appInj hA).1
--     subst hA₁
--     have hA₂ := eq_of_heq (appInj hA).2.1
--     subst hA₂
--     have hA₃ := eq_of_heq (appInj hA).2.2
--     subst hA₃
--     exact ⟨_, NormElemAux.comp HeadSymbol.noConfusion (NormElemAux.prodSnd hs f') g⟩)

-- noncomputable def comp {X Y Z : Obj C}
--   (f : NormElem Γ (hom X Y))
--   (g : NormElem Γ (hom Y Z)) :
--   NormElem Γ (hom X Z) :=
-- compAux f.2 rfl rfl g.2

-- end NormElem

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