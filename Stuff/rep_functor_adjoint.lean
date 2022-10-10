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
| _, Obj.rAdjApp F X => FuncContainsRAdj L F ∨ ObjContainsRAdj L X

def FuncContainsRAdj {C' D' : Cat} (L : Func C' D') : {C D : Cat} → (F : Func C D) → Prop
| _, _, Func.id _         => False
| _, _, Func.compVar G v  => FuncContainsRAdj L G
| _, _, Func.compRAdj G H => FuncContainsRAdj L G ∨ HEq L H

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

structure Context : Type 1 :=
( HomVar {C : Cat} (X Y : Obj C) : Type )
( hasRAdj {C D : Cat} (F : Func C D) : Bool )

variable (Γ : Context)

mutual

inductive HomAux : {C : Cat} → (X Y : Obj C) → Type where
| var {C : Cat} (X Y : Obj C) (v : Γ.HomVar X Y) : HomAux (X.cases Y).2.1 (X.cases Y).2.2
| mapVar {C : Cat} (D : Cat) {X Y : Obj C} (v : Nat) (f : HomAux X Y) :
  HomAux ((Func.var C D v).app X) ((Func.var C D v).app Y)
| mapRAdj {C D : Cat} {X Y : Obj C} (F : Func D C) (f : HomAux X Y) :
  HomAux (F.rAdj.app X) (F.rAdj.app Y)
| restrict {C D : Cat} (F : Func C D)
  {X : Obj C} {Y : Obj D} :
  Hom (F.app X) Y → HomAux X (Obj.rAdjApp F Y)
| counit {C D : Cat} (F : Func C D) (X : Obj D) :
  HomAux (F.app (F.rAdj.app X)) X

inductive Hom : {C : Cat} → (X Y : Obj C) → Type where
| id {C : Cat} (X : Obj C) : Hom X X
| comp' {C : Cat} {X Y Z : Obj C} (f : HomAux X Y) (g : Hom Y Z) : Hom X Z

end

-- mutual

-- def HomAuxContainsVar {C' : Cat} {A B : Obj C'} (v : Γ.HomVar A B) :
--   {C : Cat} → {X Y : Obj C} → HomAux Γ X Y → Prop
-- | _, _, _, HomAux.mapVar _ f         => HomAuxContainsVar v f
-- | _, _, _, HomAux.mapRAdj F f        => HomAuxContainsVar v f
-- | _, _, _, @HomAux.var _ D X' Y' w => HEq w v
-- | _, _, _, HomAux.restrict F f    => HomContainsVar v f
-- | _, _, _, HomAux.counit F X      => False

-- def HomContainsVar {C' : Cat} {A B : Obj C'} (v : Γ.HomVar A B) :
--   {C : Cat} → {X Y : Obj C} → Hom Γ X Y → Prop
-- | _, _, _, Hom.id _ => False
-- | _, _, _, Hom.comp' f g => HomAuxContainsVar v f ∨ HomContainsVar v g

-- end

mutual

inductive HomAuxContainsVar {C' : Cat} {A B : Obj C'} (v : Γ.HomVar A B) :
  {C : Cat} → {X Y : Obj C} → HomAux Γ X Y → Prop where
| self : HomAuxContainsVar v (HomAux.var A B v)
| mapRAdj : HomAuxContainsVar v f → HomAuxContainsVar v (HomAux.mapRAdj F f)
| mapVar : HomAuxContainsVar v f → HomAuxContainsVar v (HomAux.mapVar D F f)
| restrict : HomContainsVar v f → HomAuxContainsVar v (HomAux.restrict _ f)

inductive HomContainsVar {C' : Cat} {A B : Obj C'} (v : Γ.HomVar A B) :
  {C : Cat} → {X Y : Obj C} → Hom Γ X Y → Prop where
| compLeft : HomAuxContainsVar v f → HomContainsVar v (Hom.comp' f g)
| compRight : HomContainsVar v g → HomContainsVar v (Hom.comp' f g)

end

variable {Γ}

namespace Hom

variable {C D : Cat}

section defs

def ofHomAux {X Y : Obj C} (f : HomAux Γ X Y) : Hom Γ X Y :=
Hom.comp' f (Hom.id _)

noncomputable def var {X Y : Obj C} (v : Γ.HomVar X Y) : Hom Γ (X.cases Y).2.1 (X.cases Y).2.2 :=
ofHomAux (HomAux.var _ _ v)

noncomputable def comp : {C : Cat} → {X Y Z : Obj C} →
  Hom Γ X Y → Hom Γ Y Z → Hom Γ X Z
| _, _, _, _, Hom.id _, g => g
| _, _, _, _, Hom.comp' f g, h => Hom.comp' f (comp g h)

noncomputable def mapAux : {C D : Cat} → (F : Func C D) → {X Y : Obj C} →
  (f : HomAux Γ X Y) → HomAux Γ (F.app X) (F.app Y)
| _, _, Func.id _,           _, _, f => f
| _, _, (Func.compVar F v),  _, _, f => HomAux.mapVar _ v (mapAux F f)
| _, _, (Func.compRAdj F G), _, _, f => HomAux.mapRAdj G (mapAux F f)

noncomputable def map {C D : Cat} (F : Func C D) : {X Y : Obj C} →
  (f : Hom Γ X Y) → Hom Γ (F.app X) (F.app Y)
| _, _, Hom.id _ => Hom.id _
| _, _, Hom.comp' f g => Hom.comp' (mapAux F f) (map F g)

noncomputable def restrict {C D : Cat} (F : Func C D) (hF : Γ.hasRAdj F)
  {X : Obj C} {Y : Obj D}
  (f : Hom Γ (F.app X) Y) : Hom Γ X (Obj.rAdjApp F Y) :=
ofHomAux (HomAux.restrict F f)

noncomputable def counit {C D : Cat} (F : Func C D) (hF : Γ.hasRAdj F) (X : Obj D) :
  Hom Γ (F.app (F.rAdj.app X)) X :=
ofHomAux (HomAux.counit F X)

end defs

section lemmas

theorem compId : {X Y : Obj C} → (f : Hom Γ X Y) → f.comp (Hom.id _) = f
| _, _, (Hom.id _) => by rw [comp]
| _, _, (Hom.comp' f g) => by rw [Hom.comp, compId g]

theorem idComp {X Y : Obj C} (f : Hom Γ X Y) : (Hom.id _).comp f = f :=
by rw [Hom.comp]

theorem compAssoc : {W X Y Z : Obj C} →
  (f : Hom Γ W X) → (g : Hom Γ X Y) → (h : Hom Γ Y Z) →
  (f.comp g).comp h = f.comp (g.comp h)
| _, _, _, _, Hom.id _,      h, i => by rw [idComp, idComp]
| _, _, _, _, Hom.comp' f g, h, i =>
by rw [Hom.comp, Hom.comp, Hom.comp, compAssoc g]

theorem mapId {X : Obj C} (F : Func C D) : map F (@Hom.id Γ C X) = Hom.id (F.app X) :=
by rw [Hom.map]

theorem mapComp (F : Func C D) : {X Y Z : Obj C} → (f : Hom Γ X Y) → (g : Hom Γ Y Z) →
  map F (f.comp g) = (map F f).comp (map F g)
| _, _, _, Hom.id _,      g => by rw [idComp, mapId, idComp]
| _, _, _, Hom.comp' f g, h => by rw [comp, map, map, mapComp F g, comp]

end lemmas

/- Now the other normalisation stuff.
  -- Suppose we have f : X → Y where X and Y are Objects of C.
  -- If Y is rAdj, then f must be restrict to be almostNormal
  -- If Y is not rAdj then f is almostNormal if every rAdj functor contained in
    f is contained in a variable in F or X or Y.
  -- A term is normal if every subterm (define properly) is almostNormal
 -/

end Hom

mutual

noncomputable def changeVarsAux (Γ₁ Γ₂ : Context)
  (h : ∀ {C D : Cat} (F : Func C D), Γ₁.hasRAdj F → Γ₂.hasRAdj F)
  (i : {C : Cat} → {X Y : Obj C} → Γ₁.HomVar X Y → Γ₂.HomVar X Y) :
  {C : Cat} → {X Y : Obj C} → HomAux Γ₁ X Y → HomAux Γ₂ X Y
| _, _, _, HomAux.mapVar _ v f => HomAux.mapVar _ v (changeVarsAux Γ₁ Γ₂ h i f)
| _, _, _, HomAux.mapRAdj F f => HomAux.mapRAdj F (changeVarsAux Γ₁ Γ₂ h i f)
| _, _, _, HomAux.var _ _ f => HomAux.var _ _ (i f)
| _, _, _, HomAux.restrict F f => HomAux.restrict F (changeVars Γ₁ Γ₂ h i f)
| _, _, _, HomAux.counit F X => HomAux.counit F X

noncomputable def changeVars (Γ₁ Γ₂ : Context)
  (h : ∀ {C D : Cat} (F : Func C D), Γ₁.hasRAdj F → Γ₂.hasRAdj F)
  (i : {C : Cat} → {X Y : Obj C} → Γ₁.HomVar X Y → Γ₂.HomVar X Y) :
  {C : Cat} → {X Y : Obj C} → Hom Γ₁ X Y → Hom Γ₂ X Y
| _, _, _, Hom.id _ => Hom.id _
| _, _, _, Hom.comp' f g => Hom.comp' (changeVarsAux Γ₁ Γ₂ h i f) (changeVars Γ₁ Γ₂ h i g)

end

mutual

noncomputable def changeVarsAux2 (Γ₁ Γ₂ : Context) :
  {C : Cat} → {X Y : Obj C} → (f : HomAux Γ₁ X Y) →
  (h : ∀ {C D : Cat} (F : Func C D), Γ₁.hasRAdj F → Γ₂.hasRAdj F) →
  (i : {C : Cat} → {X Y : Obj C} → (v : Γ₁.HomVar X Y) →
    HomAuxContainsVar Γ₁ v f → Γ₂.HomVar X Y)  → HomAux Γ₂ X Y
| _, _, _, HomAux.mapVar _ v f, h, i =>
    HomAux.mapVar _ v (changeVarsAux2 Γ₁ Γ₂ f h
      (by
        intros C X Y v hv
        apply i
        constructor
        assumption ))
| _, _, _, HomAux.mapRAdj F f, h, i => HomAux.mapRAdj F (changeVarsAux2 Γ₁ Γ₂ f h
   (by
        intros C X Y v hv
        have := i v
        apply this
        constructor
        assumption ))
| _, _, _, HomAux.var _ _ v, h, i => HomAux.var _ _ (i v (by constructor))
| _, _, _, HomAux.restrict F f, h, i => HomAux.restrict F (changeVars2 Γ₁ Γ₂ f h
  (by
    intros
    apply i
    constructor
    assumption ))
| _, _, _, HomAux.counit F X, h, i => HomAux.counit F X

noncomputable def changeVars2 (Γ₁ Γ₂ : Context) :
  {C : Cat} → {X Y : Obj C} → (f : Hom Γ₁ X Y) →
  (h : ∀ {C D : Cat} (F : Func C D), Γ₁.hasRAdj F → Γ₂.hasRAdj F) →
  (i : {C : Cat} → {X Y : Obj C} → (v : Γ₁.HomVar X Y) →
    HomContainsVar Γ₁ v f → Γ₂.HomVar X Y) → Hom Γ₂ X Y
| _, _, _, Hom.id _, _, _ => Hom.id _
| _, _, _, Hom.comp' f g, h, i =>
  Hom.comp' (changeVarsAux2 Γ₁ Γ₂ f h
    (by
      intros
      apply i
      constructor
      assumption))
    (changeVars2 Γ₁ Γ₂ g h
      (by
        intros C X Y v hv
        apply i v
        apply HomContainsVar.compRight
        assumption ))

end

noncomputable def toPresheaf (Γ₁ Γ₂ : Context)
  (h : ∀ {C D : Cat} (F : Func C D), Γ₁.hasRAdj F → Γ₂.hasRAdj F)
  (i : {C : Cat} → {X Y : Obj C} → Γ₁.HomVar X Y → Γ₂.HomVar X Y)
  {C : Cat} {X Y : Obj C} (f : Hom X Y) :
