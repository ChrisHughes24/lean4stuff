inductive Cat :=
| var (n : Nat) : Cat
deriving DecidableEq

mutual

inductive Obj :  Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| varApp {C D : Cat} (v : Nat) (X : Obj C) : Obj D
| rAdjApp {C D : Cat} (F : Func C D) (X : Obj D) : Obj C

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| compVar {C D E : Cat} (F : Func C D) (v : Nat) : Func C E
| compRAdj {C D E : Cat} (F : Func C D) (G : Func E D) : Func C E

end

@[instance] axiom Func.DecidableEq : {C D : Cat} → DecidableEq (Func C D)

@[instance] axiom Sigma.DecidableEq {α : Type} (β : α → Type) : DecidableEq (Sigma β)

noncomputable def Func.compAux {D E : Cat} (G : Func D E) : (C : Cat) → (F : Func C D) → Func C E :=
@Func.recOn (λ _ _ => Unit) (λ D E G => (C : Cat) → (F : Func C D) → Func C E)
  D E G
  (λ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ F => F)
  (λ D v ih C F => compVar (ih _ F) v)
  (λ F G ih _ C H => compRAdj (ih _ H) G)

noncomputable def Func.comp {C D E : Cat} (F : Func C D) (G : Func D E) : Func C E :=
Func.compAux G _ F

noncomputable def Func.app {C D : Cat} (F : Func C D) : (X : Obj C) → Obj D :=
@Func.recOn (λ _ _ => Unit) (λ C D _ => Obj C → Obj D)
  C D F
  (λ _ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ X => X)
  (λ F v ih X => Obj.varApp v (ih X))
  (λ F G ih _ X => Obj.rAdjApp G (ih X))

theorem Func.idApp {C : Cat} (X : Obj C) : (Func.id C).app X = X := rfl

theorem Func.compVarApp {C D E : Cat} (F : Func C D) (v : Nat) (X : Obj C) :
  (@Func.compVar C D E F v).app X = Obj.varApp v (F.app X) := rfl

theorem Func.compRAdjApp {C D E : Cat} (F : Func C D) (G : Func E D) (X : Obj C) :
  (Func.compRAdj F G).app X = Obj.rAdjApp G (F.app X) := rfl

def Func.var (C D : Cat) (v : Nat) : Func C D :=
Func.compVar (Func.id _) v

def Func.rAdj {C D : Cat} (F : Func D C) : Func C D :=
Func.compRAdj (Func.id _) F

theorem rAdjAppEq {C D : Cat} (F : Func C D) (X : Obj D) :
  F.rAdj.app X = Obj.rAdjApp F X := rfl

-- noncomputable def Obj.cases : {C : Cat} →
--   (X Y : Obj C) → Σ D : Cat, Obj D × Obj D
-- | C, X, Obj.rAdjApp F Y => cases (F.app X) Y
-- | C, X, Obj.var _ v => ⟨C, X, Obj.var _ v⟩
-- | _, X, Obj.varApp v Y => ⟨_, X, Obj.varApp v Y⟩

noncomputable def Obj.cases' {C : Cat}
  (Y : Obj C) : (X : Obj C) → Σ D : Cat, Obj D × Obj D :=
@Obj.recOn (λ C X => Obj C → Σ D : Cat, Obj D × Obj D)
  (λ _ _ _ => Unit)
  C Y
  (λ C v X => ⟨C, X, Obj.var C v⟩)
  (λ v Y ih X => ⟨_, X, Obj.varApp v Y⟩)
  (λ F Y _ ih X => ih (F.app X))
  (λ _ => ())
  (λ _ _ _ => ())
  (λ _ _ _ _ => ())

noncomputable def Obj.cases {C : Cat}
  (X Y : Obj C) : Σ D : Cat, Obj D × Obj D :=
Obj.cases' Y X

inductive RAdjStack : (C D : Cat) → Type
| single : {C D : Cat} → Func D C → RAdjStack C D
| app : {C D E : Cat} → Func E D → RAdjStack C D → RAdjStack C E

noncomputable def RAdjStack.toRAdjFunc : {C D : Cat} → (F : RAdjStack C D) → Func C D
| _, _, single F => F.rAdj
| _, _, app F G => (toRAdjFunc G).comp F.rAdj

noncomputable def RAdjStack.toFunc : {C D : Cat} → (F : RAdjStack C D) → Func D C
| _, _, single F => F
| _, _, app F G => F.comp (toFunc G)

structure HomData : Type :=
( isVarApp : Option (Cat × Nat) ) --Left
( isCounit : Option (Σ C D : Cat, Func C D) ) --Right
( isRestrict : Bool ) -- Right
( isComp : Bool )
( isId : Bool )

inductive HomAux : {C : Cat} → (X Y : Obj C) → HomData → Type
| mapVar {C D : Cat} {X Y : Obj C} {o : HomData} (v : Nat) (f : HomAux X Y o)
  (hf : o.isId = false) : HomAux ((Func.var C D v).app X) ((Func.var C D v).app Y)
  ⟨some (C, v), none, false, false, false⟩
| varCases {C : Cat} (X Y : Obj C) (v : Nat) :
  HomAux (X.cases Y).2.1 (X.cases Y).2.2 ⟨none, none, false, false, false⟩
| counit {C D : Cat} (F : Func C D) (X : Obj D) :
  HomAux (F.app (F.rAdj.app X)) X ⟨none, some ⟨_, _, F⟩, false, false, false⟩
| restrict {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj D} {o : HomData}
  (f : HomAux (F.app X) Y o) (ho : o.isCounit ≠ some ⟨_, _, F⟩) :
  HomAux X (Obj.rAdjApp F Y) ⟨none, none, true, false, false⟩
| comp {C : Cat} {X Y Z : Obj C} {o₁ o₂ : HomData}
  (h : o₁.isVarApp ≠ o₂.isVarApp ∨ o₁.isVarApp = none)
  (ho₁C : o₁.isComp = false) (ho₂I : o₂.isId = false)
  (ho₁I : o₁.isId = false)
  (f : HomAux X Y o₁) (g : HomAux Y Z o₂) : HomAux X Z
  ⟨o₁.isVarApp, o₂.isCounit, o₂.isRestrict, true, false⟩
| id {C : Cat} (X : Obj C) : HomAux X X ⟨none, none, false, false, true⟩

def Hom (X Y : Obj C) := Σ o : HomData, HomAux X Y o

noncomputable def Hom.ofCases : {C : Cat} → (X Y : Obj C) → {o : HomData} →
  (f : HomAux (X.cases Y).2.1 (X.cases Y).2.2 o) →
  (hf : o.isCounit = none) → Σ' g : Hom X Y, g.1.isCounit = none
| C, X, Obj.rAdjApp F Y, o, f, hf =>
  ⟨⟨_, HomAux.restrict _ (ofCases (F.app X) Y f hf).1.2
    (by rw [(ofCases (F.app X) Y f hf).2]
        simp)⟩, rfl⟩
| C, X, Obj.varApp v Y, o, f, hf => ⟨⟨_, f⟩, hf⟩
| C, X, Obj.var _ _, o, f, hf => ⟨⟨_, f⟩, hf⟩

noncomputable def Hom.var {C : Cat} (X Y : Obj C) (v : Nat) : Hom X Y :=
(Hom.ofCases _ _ (HomAux.varCases _ _ v) rfl).1

noncomputable def Hom.id (X : Obj C) : Hom X X :=
⟨_, HomAux.id _⟩

noncomputable def isIdCases
  {motive : {C : Cat} → {X Y : Obj C}  → Hom X Y → Type}
  (motiveId : {C : Cat} → (X : Obj C) → motive (Hom.id X))
  (motiveNotId : {C : Cat} → (X Y : Obj C) → (f : Hom X Y) →
    f.1.isId = false → motive f) : {C : Cat} →
  {X Y : Obj C} → (f : Hom X Y) →
  motive f
| _, _, _, ⟨_, HomAux.mapVar v f hf⟩ => motiveNotId _ _ ⟨_, HomAux.mapVar v f hf⟩ rfl
| _, _, _, ⟨_, HomAux.varCases X Y v⟩ => motiveNotId _ _ ⟨_, HomAux.varCases X Y v⟩ rfl
| _, _, _, ⟨_, HomAux.restrict F f ho⟩ => motiveNotId _ _ ⟨_, HomAux.restrict F f ho⟩ rfl
| _, _, _, ⟨_, HomAux.counit F X⟩ => motiveNotId _ _ ⟨_, HomAux.counit F X⟩ rfl
| _, _, _, ⟨_, HomAux.comp h₁ h₂ h₃ h₄ f g⟩ => motiveNotId _ _ ⟨_, HomAux.comp h₁ h₂ h₃ h₄ f g⟩ rfl
| _, _, _, ⟨_, HomAux.id _⟩ => motiveId _

noncomputable def Hom.mapVar {C D : Cat} {X Y : Obj C}
  (v : Nat) (f : Hom X Y) : Hom ((Func.var C D v).app X) ((Func.var C D v).app Y) :=
@isIdCases (@λ C X Y f => Hom ((Func.var C D v).app X) ((Func.var C D v).app Y))
  (λ _ => Hom.id _)
  (λ X Y f hf => ⟨_, HomAux.mapVar v f.2 hf⟩)
  C X Y f

noncomputable def Hom.counit {C D : Cat} (F : Func C D) (X : Obj D) :
  Hom (F.app (F.rAdj.app X)) X :=
⟨_, HomAux.counit F X⟩

noncomputable def isCounitCases {C D : Cat} (F : Func C D)
  {motive : {C : Cat} → {X Y : Obj C} → Hom X Y → Type}
  (motiveCounit : (X : Obj D) → motive (Hom.counit F X))
  (motiveCounitComp : (X Y : Obj D) → (g : HomAux X Y o) → (h₃ : o.isId = false) →
    motive ⟨_, HomAux.comp (by simp) (by simp) h₃ (by simp) (HomAux.counit F X) g⟩)
  (motiveNotCounit : {C : Cat} → (X Y : Obj C) → (f : Hom X Y) →
    f.1.isCounit ≠ some ⟨_, _, F⟩ → motive f) : {C : Cat} →
  {X Y : Obj C} → (f : Hom X Y) →
  motive f
| _, _, _, ⟨_, HomAux.mapVar v f hf⟩ => motiveNotCounit _ _ ⟨_, HomAux.mapVar v f hf⟩ (by simp)
| _, _, _, ⟨_, HomAux.varCases X Y v⟩ => motiveNotCounit _ _ ⟨_, HomAux.varCases X Y v⟩ (by simp)
| _, _, _, ⟨_, HomAux.restrict F f ho⟩ => motiveNotCounit _ _ ⟨_, HomAux.restrict F f ho⟩ (by simp)
| _, _, _, ⟨_, HomAux.counit G Y⟩ =>
  if h : (⟨_, _, G⟩ : Σ C D : Cat, Func C D) = ⟨_, _, F⟩
  then by
    cases h
    exact motiveCounit _
  else motiveNotCounit _ _ ⟨_, HomAux.counit G Y⟩ (λ h2 => by simp at *; contradiction)
| _, _, _, ⟨_, @HomAux.comp _ _ Y _ o₁ ⟨_, none, _, _, _⟩ h₁ h₂ h₃ h₄ f g⟩ =>
  motiveNotCounit _ _ ⟨_, @HomAux.comp _ _ Y _ o₁ _ h₁ h₂ h₃ h₄ f g⟩ (by simp)
| _, _, _, ⟨_, @HomAux.comp _ _ _ _ _ ⟨_, some ⟨_, _, G⟩, _, _, _⟩ h₁ h₂ h₃ h₄ f g⟩ =>
  if h : (⟨_, _, G⟩ : Σ C D : Cat, Func C D) = ⟨_, _, F⟩
  then by
    cases h
    exact motiveCounitComp _ _ _ _
  else sorry
| _, _, _, ⟨_, HomAux.id X⟩ => motiveNotCounit _ _ ⟨_, HomAux.id X⟩ (by simp)


noncomputable def Hom.restrict : {C D : Cat} → (F : Func C D) → {X : Obj C} →
  {Y : Obj D} → (f : Hom (F.app X) Y) → Hom X (Obj.rAdjApp F Y)
| _, _


