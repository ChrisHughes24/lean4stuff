inductive Cat :=
| var (n : Nat) : Cat

mutual

inductive Obj : Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| varApp {C D : Cat} (v : Nat) (X : Obj C) : Obj D
| rAdjApp {C D : Cat} (F : Func C D) (X : Obj D) : Obj C

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| compVar {C D E : Cat} (F : Func C D) (v : Nat) : Func C E
| compRAdj {C D E : Cat} (F : Func C D) (G : Func E D) : Func C E

end

mutual

def ObjContainsRAdj {C' D' : Cat} (L : Func C' D') : {C : Cat} → (X : Obj C) → Prop
| _, Obj.var _ _     => False
| _, Obj.varApp _ X  => ObjContainsRAdj L X
| _, Obj.rAdjApp F X => FuncContainsRAdj L F ∨ ObjContainsRAdj L X ∨ HEq L F

def FuncContainsRAdj {C' D' : Cat} (L : Func C' D') : {C D : Cat} → (F : Func C D) → Prop
| _, _, Func.id _         => False
| _, _, Func.compVar G v  => FuncContainsRAdj L G
| _, _, Func.compRAdj G H => FuncContainsRAdj L G ∨ FuncContainsRAdj L H ∨ HEq L H

end

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

noncomputable def Obj.cases : {C : Cat} → (X Y : Obj C) → Σ D : Cat, Obj D × Obj D
| C, X, rAdjApp F Y => cases (F.app X) Y
| C, X,           Y => ⟨C, X, Y⟩

theorem FuncAppContainsRAdj {C' D' : Cat} (G : Func C' D') :
  {C D : Cat} → (F : Func C D) → (X : Obj C) →
  ObjContainsRAdj G (F.app X) ↔ FuncContainsRAdj G F ∨ ObjContainsRAdj G X
| _, _, (Func.id _), X => by
rw [Func.idApp, FuncContainsRAdj, false_or, iff_self]
trivial
| _, _, (Func.compVar F v), X => by
rw [Func.compVarApp, ObjContainsRAdj, FuncContainsRAdj, FuncAppContainsRAdj G F, iff_self]
trivial
| _, _, (Func.compRAdj I H), X => by
rw [Func.compRAdjApp, ObjContainsRAdj, FuncContainsRAdj, FuncAppContainsRAdj G I]
sorry


theorem ObjContainsRAdjCases1 : {C D E : Cat} → {X Y : Obj E} → {F : Func C D} →
  ObjContainsRAdj F (X.cases Y).2.1 → ObjContainsRAdj F X ∨ ObjContainsRAdj F Y
| C, D, E, X, Obj.rAdjApp G Y, F, h => by
  rw [Obj.cases] at h
  have h' := ObjContainsRAdjCases1 h
  rw [FuncAppContainsRAdj] at h'
  rw [ObjContainsRAdj]
  sorry
| C, D, E, X, Obj.var _ _, F, h => by
  rw [Obj.cases] at h
  simp [Obj.cases] at h
  exact Or.inl h
  intros _ _ _ h
  injection h
| C, D, E, X, Obj.varApp v Y, F, h => by
  rw [Obj.cases] at h
  simp at h
  exact Or.inl h
  intros _ _ _ h
  injection h

theorem ObjContainsRAdjCases2 : {C D E : Cat} → {X Y : Obj E} → {F : Func C D} →
  ObjContainsRAdj F (X.cases Y).2.2 → ObjContainsRAdj F X ∨ ObjContainsRAdj F Y
| C, D, E, X, Obj.rAdjApp G Y, F, h => by
  rw [Obj.cases] at h
  have h' := ObjContainsRAdjCases2 h
  rw [FuncAppContainsRAdj] at h'
  rw [ObjContainsRAdj]
  sorry
| C, D, E, X, Obj.var _ _, F, h => by
  rw [Obj.cases] at h
  simp [Obj.cases] at h
  exact Or.inr h
  intros _ _ _ h
  injection h
| C, D, E, X, Obj.varApp v Y, F, h => by
  rw [Obj.cases] at h
  simp at h
  exact Or.inr h
  intros _ _ _ h
  injection h

mutual

inductive HomAux : {C : Cat} → (X Y : Obj C) → Type where
| mapVar {C D : Cat} {X Y : Obj C} (v : Nat) (f : HomAux X Y) :
  HomAux ((Func.var C D v).app X) ((Func.var C D v).app Y)
| mapRAdj {C D : Cat} {X Y : Obj C} (F : Func D C) (f : HomAux X Y) :
  HomAux (F.rAdj.app X) (F.rAdj.app Y)
| var {C : Cat} {X Y : Obj C} (v : Nat) : HomAux (X.cases Y).2.1 (X.cases Y).2.2
| restrict {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj D} :
  Hom (F.app X) Y → HomAux X (Obj.rAdjApp F Y)
| counit {C D : Cat} (F : Func C D) (X : Obj D) :
  HomAux (F.app (F.rAdj.app X)) X

inductive Hom : {C : Cat} → (X Y : Obj C) → Type where
| id {C : Cat} (X : Obj C) : Hom X X
| comp' {C : Cat} {X Y Z : Obj C} (f : HomAux X Y) (g : Hom Y Z) : Hom X Z

end

mutual

noncomputable def HomAuxContainsVar {C' : Cat} (A B : Obj C') (v : Nat) :
  {C : Cat} → {X Y : Obj C} → HomAux X Y → Prop
| _, _, _, HomAux.mapVar _ f      => HomAuxContainsVar A B v f
| _, _, _, HomAux.mapRAdj F f     => HomAuxContainsVar A B v f
| _, _, _, HomAux.var w        => _
| _, _, _, HomAux.restrict F f => HomContainsVar A B v f
| _, _, _, HomAux.counit F X   => False

noncomputable def HomContainsVar {C' : Cat} (A B : Obj C') (v : Nat) :
  {C : Cat} → {X Y : Obj C} → Hom X Y → Prop
| _, _, _, Hom.id _ => False
| _, _, _, Hom.comp' f g => HomAuxContainsVar A B v f ∨ HomContainsVar A B v g

end

mutual

noncomputable def HomAuxContainsRAdj {C' D' : Cat} (F : Func C' D') :
  {C : Cat} → {X Y : Obj C} → HomAux X Y → Prop
| _, _, _, HomAux.mapVar _ f   => HomAuxContainsRAdj F f
| _, _, _, HomAux.mapRAdj G f  => HomAuxContainsRAdj F f ∨ HEq F G
  ∨ FuncContainsRAdj F G
| _, _, _, @HomAux.var _ X Y w => ObjContainsRAdj F X ∨ ObjContainsRAdj F Y
| _, _, _, HomAux.restrict G f => HomContainsRAdj F f ∨ HEq F G ∨ FuncContainsRAdj F G
| _, _, _, HomAux.counit G X   => ObjContainsRAdj F X ∨ HEq F G ∨ FuncContainsRAdj F G

noncomputable def HomContainsRAdj {C' D' : Cat} (F : Func C' D') :
  {C : Cat} → {X Y : Obj C} → Hom X Y → Prop
| _, X, _, Hom.id _ => ObjContainsRAdj F X
| _, _, _, Hom.comp' f g => HomAuxContainsRAdj F f ∨ HomContainsRAdj F g

end

variable {Γ}

namespace Hom

variable {C D : Cat}

section defs

def ofHomAux {X Y : Obj C} (f : HomAux X Y) : Hom X Y :=
Hom.comp' f (Hom.id _)

noncomputable def var (X Y : Obj C) (v : Nat) : Hom (X.cases Y).2.1 (X.cases Y).2.2 :=
ofHomAux (HomAux.var v)

noncomputable def comp : {C : Cat} → {X Y Z : Obj C} →
  Hom X Y → Hom Y Z → Hom X Z
| _, _, _, _, Hom.id _, g => g
| _, _, _, _, Hom.comp' f g, h => Hom.comp' f (comp g h)

noncomputable def mapAux : {C D : Cat} → (F : Func C D) → {X Y : Obj C} →
  (f : HomAux X Y) → HomAux (F.app X) (F.app Y)
| _, _, Func.id _,           _, _, f => f
| _, _, (Func.compVar F v),  _, _, f => HomAux.mapVar v (mapAux F f)
| _, _, (Func.compRAdj F G), _, _, f => HomAux.mapRAdj G (mapAux F f)

noncomputable def map {C D : Cat} (F : Func C D) : {X Y : Obj C} →
  (f : Hom X Y) → Hom (F.app X) (F.app Y)
| _, _, Hom.id _ => Hom.id _
| _, _, Hom.comp' f g => Hom.comp' (mapAux F f) (map F g)

noncomputable def restrict {C D : Cat} (F : Func C D)
  {X : Obj C} {Y : Obj D}
  (f : Hom (F.app X) Y) : Hom X (Obj.rAdjApp F Y) :=
ofHomAux (HomAux.restrict F f)

noncomputable def counit {C D : Cat} (F : Func C D) (X : Obj D) :
  Hom (F.app (F.rAdj.app X)) X :=
ofHomAux (HomAux.counit F X)

end defs

section lemmas

theorem compId : {X Y : Obj C} → (f : Hom X Y) → f.comp (Hom.id _) = f
| _, _, (Hom.id _) => by rw [comp]
| _, _, (Hom.comp' f g) => by rw [Hom.comp, compId g]

theorem idComp {X Y : Obj C} (f : Hom X Y) : (Hom.id _).comp f = f :=
by rw [Hom.comp]

theorem compAssoc : {W X Y Z : Obj C} →
  (f : Hom W X) → (g : Hom X Y) → (h : Hom Y Z) →
  (f.comp g).comp h = f.comp (g.comp h)
| _, _, _, _, Hom.id _,      h, i => by rw [idComp, idComp]
| _, _, _, _, Hom.comp' f g, h, i =>
by rw [Hom.comp, Hom.comp, Hom.comp, compAssoc g]

theorem mapId {X : Obj C} (F : Func C D) : map F (@Hom.id C X) = Hom.id (F.app X) :=
by rw [Hom.map]

theorem mapComp (F : Func C D) : {X Y Z : Obj C} → (f : Hom X Y) → (g : Hom Y Z) →
  map F (f.comp g) = (map F f).comp (map F g)
| _, _, _, Hom.id _,      g => by rw [idComp, mapId, idComp]
| _, _, _, Hom.comp' f g, h => by rw [comp, map, map, mapComp F g, comp]

end lemmas

/- Now the other normalisation stuff.
  -- Suppose we have f : X → Y where X and Y are Objects of C and the context is cased.
  -- If Y is rAdj, then f must be restrict to be almostNormal
  -- If Y is not rAdj then f is almostNormal if every rAdj functor contained in
    f is contained in the domain of a variable in f or cases of the codomain.
  -- A term is normal if every subterm (define properly) is almostNormal
 -/

end Hom

structure Context : Type :=
( HomVar {C : Cat} (X Y : Obj C) : Nat → Prop )
( hasRAdj {C D : Cat} (F : Func C D) : Prop )
-- ( h : ∀ {C : Cat} (X Y : Obj C) (v : Nat),
--     HomVar X Y v → ∀ {C' D' : Cat} (F : Func C' D'),
--     ObjContainsRAdj F X ∨ ObjContainsRAdj F Y →
--     hasRAdj F )

def SmallestContext {C : Cat} {X Y : Obj C} (f : Hom X Y) : Context :=
{ HomVar  := λ X Y n => HomContainsVar X Y n f,
  hasRAdj := λ F     => HomContainsRAdj F f }

def lessRAdj (Γ₁ Γ₂ : Context) : Prop :=
@Context.HomVar Γ₁ = @Context.HomVar Γ₂ ∧
  ∀ {C D : Cat} (F : Func C D), Γ₁.hasRAdj F → Γ₂.hasRAdj F

variable (Γ : Context)

def ObjC (C : Cat) : Type :=
Σ' X : Obj C, ∀ (C' D' : Cat) (F : Func C' D'), ObjContainsRAdj F X → Γ.hasRAdj F

def FuncC (C D : Cat) : Type :=
Σ' F : Func C D, ∀ (C' D' : Cat) (G : Func C' D'), FuncContainsRAdj G F → Γ.hasRAdj G

def HomC {C : Cat} (X Y : ObjC Γ C) : Type :=
Σ' f : Hom X.1 Y.1,
  (∀ (C' D' : Cat) (F : Func C' D'), HomContainsRAdj F f → Γ.hasRAdj F) ∧
  ∀ (C' : Cat) (X' Y' : ObjC Γ C') (v : Nat), HomContainsVar X'.1 Y'.1 v f →
    Γ.HomVar X'.1 Y'.1 v

variable {Γ}

noncomputable def ObjC.cases {C : Cat} (X Y : ObjC Γ C) : Σ D : Cat, ObjC Γ D × ObjC Γ D :=
let B := Obj.cases X.1 Y.1
⟨B.1, ⟨B.2.1,
  by
  intros C' D' F h
  have := ObjContainsRAdjCases1 h
  cases this
  apply X.2
  assumption
  apply Y.2
  assumption⟩,
  ⟨B.2.2,
  by
  intros C' D' F h
  have := ObjContainsRAdjCases2 h
  cases this
  apply X.2
  assumption
  apply Y.2
  assumption⟩⟩

noncomputable def FuncC.app {C D : Cat} (F : FuncC Γ C D) (X : ObjC Γ C) : ObjC Γ D :=
⟨F.1.app X.1, sorry⟩

namespace HomC

noncomputable def var (X Y : ObjC Γ C) (v : Nat) (h : Γ.HomVar X.1 Y.1 v) :
  HomC Γ (X.cases Y).2.1 (X.cases Y).2.2 :=
⟨Hom.var X.1 Y.1 v, by
  apply And.intro
  intros C' D' F h2
  rw [Hom.var, Hom.ofHomAux, HomContainsRAdj, HomContainsRAdj] at h2
  sorry
  intros C' X' Y' w h2
  rw [Hom.var, Hom.ofHomAux, HomContainsVar] at h2
  sorry ⟩

noncomputable def id {C : Cat} (X : ObjC Γ C) : HomC Γ X X :=
⟨Hom.id X.1, sorry⟩

noncomputable def comp {C : Cat} {X Y Z : ObjC Γ C} :
  HomC Γ X Y → HomC Γ Y Z → HomC Γ X Z :=
λ f g => ⟨Hom.comp f.1 g.1, sorry⟩

noncomputable def map {C D : Cat} (F : FuncC Γ C D) {X Y : ObjC Γ C}
  (f : HomC Γ X Y) : HomC Γ (F.app X) (F.app Y) :=
⟨Hom.map F.1 f.1, sorry⟩

noncomputable def restrict {C D : Cat} (F : FuncC Γ C D)
  {X : ObjC Γ C} {Y : ObjC Γ D}
  (f : Hom (F.app X) Y) : Hom X (Obj.rAdjApp F Y) :=
ofHomAux (HomAux.restrict F f)

noncomputable def counit {C D : Cat} (F : Func C D) (X : Obj D) :
  Hom (F.app (F.rAdj.app X)) X :=
ofHomAux (HomAux.counit F X)

end HomC