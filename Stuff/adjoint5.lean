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

@[simp] theorem Func.idApp {C : Cat} (X : Obj C) : (Func.id C).app X = X := rfl

@[simp] theorem Func.compVarApp {C D E : Cat} (F : Func C D) (v : Nat) (X : Obj C) :
  (@Func.compVar C D E F v).app X = Obj.varApp v (F.app X) := rfl

@[simp] theorem Func.compRAdjApp {C D E : Cat} (F : Func C D) (G : Func E D) (X : Obj C) :
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

inductive Hom : {C : Cat} → (X Y : Obj C) → Type
| mapVar {C D : Cat} {X Y : Obj C} (v : Nat) (f : Hom X Y) :
  Hom ((Func.var C D v).app X) ((Func.var C D v).app Y)
| varCases {C : Cat} (X Y : Obj C) (v : Nat) :
  Hom (X.cases Y).2.1 (X.cases Y).2.2
| counit {C D : Cat} (F : Func C D) (X : Obj D) :
  Hom (F.app (F.rAdj.app X)) X
| restrict {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj D}
  (f : Hom (F.app X) Y) : Hom X (Obj.rAdjApp F Y)
| comp {C : Cat} {X Y Z : Obj C}
  (f : Hom X Y) (g : Hom Y Z) : Hom X Z
| id {C : Cat} (X : Obj C) : Hom X X

noncomputable def Hom.ofCases : {C : Cat} → (X Y : Obj C) →
  (f : Hom (X.cases Y).2.1 (X.cases Y).2.2) → Hom X Y
| C, X, Obj.rAdjApp F Y, f =>
  Hom.restrict _ (ofCases (F.app X) Y f)
| C, X, Obj.varApp v Y, f => f
| C, X, Obj.var _ _,  f => f

noncomputable def Hom.var {C : Cat} (X Y : Obj C) (v : Nat) : Hom X Y :=
Hom.ofCases _ _ (Hom.varCases _ _ v)

/-
Rewriting rules
  F(f) ∘ F(g) => F (f ∘ g)
  restrict F (counit X) => id (F.rAdj.app X)
  restrict F (F.map f ∘ counit Y) => f
  f ∘ restrict F g = restrict f (F.map f ∘ g)
  F.map (restrict F f) ∘ counit _ = f
  F.map (g ∘ restrict F f) ∘ counit _ = F.map g ∘ f
-/

mutual

inductive Hom₁Aux : {C : Cat} → (X Y : Obj C) → Type
| mapVar {C D : Cat} {X Y : Obj C} (v : Nat) (f : Hom₁ X Y) :
  Hom₁Aux (Obj.varApp v X) (Obj.varApp v Y : Obj D)
| varCases {C : Cat} (X Y : Obj C) (v : Nat) :
  Hom₁Aux (X.cases Y).2.1 (X.cases Y).2.2
| counit {C D : Cat} (F : Func C D) (X : Obj D) :
  Hom₁Aux (F.app (F.rAdj.app X)) X
| restrict {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj D}
  (f : Hom₁ (F.app X) Y) : Hom₁Aux X (Obj.rAdjApp F Y)

inductive Hom₁ : {C : Cat} → (X Y : Obj C) → Type
| comp {C : Cat} {X Y Z : Obj C} (f : Hom₁ X Y) (g : Hom₁Aux Y Z) : Hom₁ X Z
| id {C : Cat} (X : Obj C) : Hom₁ X X

end

def Hom₁AuxToHom₁ {C : Cat} {X Y : Obj C} (f : Hom₁Aux X Y) : Hom₁ X Y :=
Hom₁.comp (Hom₁.id _) f

def Func.map : {C D : Cat} → {X Y : Obj C} → (F : Func C D) →
  (f : Hom₁ X Y) → Hom₁ (F.app X) (F.app Y)
| _, _, _, _, Func.id _, f => f
| _, _, _, _, Func.compVar F v, f => Hom₁AuxToHom₁ (Hom₁Aux.mapVar v (map F f))
| _, _, _, _, Func.compRAdj F G, f =>
  Hom₁AuxToHom₁ (Hom₁Aux.restrict _
    (by
    simp
  ))


mutual

def Hom₁AuxComp : {C : Cat} → {X Y Y' Z : Obj C} → Hom₁Aux X Y → Hom₁Aux Y' Z →
  Y = Y' → Hom₁ X Z
| _, _, _, _, _, Hom₁Aux.mapVar v f, Hom₁Aux.mapVar w g, h => by
  cases h
  exact Hom₁AuxToHom₁ (Hom₁Aux.mapVar v (Hom₁Comp f g rfl))
| _, _, _, _, _, f, Hom₁Aux.restrict F g, h => by
  cases h
  exact Hom₁Aux.restrict F (Hom₁Comp (Hom₁AuxToHom₁ f) g _)
| _, _, _, _, _, _, _, _ => sorry

def Hom₁Comp : {C : Cat} → {X Y Y' Z : Obj C} → Hom₁ X Y → Hom₁ Y' Z →
  Y = Y' → Hom₁ X Z
| _, _, _, _, _, _, _, _ => sorry

end