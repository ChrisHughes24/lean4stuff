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

def Func.var (C D : Cat) (v : Nat) : Func C D :=
Func.compVar (Func.id _) v

def Func.rAdj {C D : Cat} (F : Func D C) : Func C D :=
Func.compRAdj (Func.id _) F

structure Context : Type 1 :=
( HomVar {C : Cat} (X Y : Obj C) : Type )
( hasRAdj {C D : Cat} (F : Func C D) : Bool )

noncomputable def Obj.cases (Γ : Context) : {C : Cat} → (X Y : Obj C) → Σ D : Cat, Obj D × Obj D
| C, X, rAdjApp F Y => if Γ.hasRAdj F then cases Γ (F.app X) Y else ⟨C, X, rAdjApp F Y⟩
| C, X,           Y => ⟨C, X, Y⟩

def Context.cases (Γ : Context) : Context :=
{ HomVar := λ X Y =>
    Σ' (D : Cat) (X' Y' : Obj D) (h : X'.cases Γ Y' = ⟨_, X, Y⟩), Γ.HomVar X' Y'
  hasRAdj := Γ.hasRAdj }

variable (Γ : Context)

mutual

inductive HomAux : {C : Cat} → (X Y : Obj C) → Type where
| mapVar {C D : Cat} {X Y : Obj C} (v : Nat) (f : HomAux X Y) :
  HomAux ((Func.var C D v).app X) ((Func.var C D v).app Y)
| mapRAdj {C D : Cat} {X Y : Obj C} (F : Func D C) (f : HomAux X Y) :
  HomAux (F.rAdj.app X) (F.rAdj.app Y)
| var {C : Cat} {X Y : Obj C} (v : Γ.HomVar X Y) : HomAux X Y
| restrict {C D : Cat} (F : Func C D) (hF : Γ.hasRAdj F)
  {X : Obj C} {Y : Obj D} :
  Hom (F.app X) Y → HomAux X (F.rAdj.app Y)
| counit {C D : Cat} (F : Func C D) (hF : Γ.hasRAdj F) (X : Obj D) :
  HomAux (F.app (F.rAdj.app X)) X

inductive Hom : {C : Cat} → (X Y : Obj C) → Type where
| id {C : Cat} (X : Obj C) : Hom X X
| comp' {C : Cat} {X Y Z : Obj C} (f : HomAux X Y) (g : Hom Y Z) : Hom X Z

end

mutual

def HomAuxContainsVar {C' : Cat} {A B : Obj C'} (v : Γ.HomVar A B) :
  {C : Cat} → {X Y : Obj C} → HomAux Γ X Y → Prop
| _, _, _, HomAux.mapVar _ f      => HomAuxContainsVar v f
| _, _, _, HomAux.mapRAdj F f     => HomAuxContainsVar v f
| _, _, _, HomAux.var w           => HEq w v
| _, _, _, HomAux.restrict F hF f => HomContainsVar v f
| _, _, _, HomAux.counit F hF X   => False

def HomContainsVar {C' : Cat} {A B : Obj C'} (v : Γ.HomVar A B) :
  {C : Cat} → {X Y : Obj C} → Hom Γ X Y → Prop
| _, _, _, Hom.id _ => False
| _, _, _, Hom.comp' f g => HomAuxContainsVar v f ∨ HomContainsVar v g

end

variable {Γ}

namespace Hom

variable {C D : Cat}

section defs

def ofHomAux {X Y : Obj C} (f : HomAux Γ X Y) : Hom Γ X Y :=
Hom.comp' f (Hom.id _)

def var {X Y : Obj C} (v : Γ.HomVar X Y) : Hom Γ X Y :=
ofHomAux (HomAux.var v)

noncomputable def comp : {C : Cat} → {X Y Z : Obj C} →
  Hom Γ X Y → Hom Γ Y Z → Hom Γ X Z
| _, _, _, _, Hom.id _, g => g
| _, _, _, _, Hom.comp' f g, h => Hom.comp' f (comp g h)

noncomputable def mapAux : {C D : Cat} → (F : Func C D) → {X Y : Obj C} →
  (f : HomAux Γ X Y) → HomAux Γ (F.app X) (F.app Y)
| _, _, Func.id _,           _, _, f => f
| _, _, (Func.compVar F v),  _, _, f => HomAux.mapVar v (mapAux F f)
| _, _, (Func.compRAdj F G), _, _, f => HomAux.mapRAdj G (mapAux F f)

noncomputable def map {C D : Cat} (F : Func C D) : {X Y : Obj C} →
  (f : Hom Γ X Y) → Hom Γ (F.app X) (F.app Y)
| _, _, Hom.id _ => Hom.id _
| _, _, Hom.comp' f g => Hom.comp' (mapAux F f) (map F g)

noncomputable def restrict {C D : Cat} (F : Func C D) (hF : Γ.hasRAdj F)
  {X : Obj C} {Y : Obj D}
  (f : Hom Γ (F.app X) Y) : Hom Γ X (F.rAdj.app Y) :=
ofHomAux (HomAux.restrict F hF f)

noncomputable def counit {C D : Cat} (F : Func C D) (hF : Γ.hasRAdj F) (X : Obj D) :
  Hom Γ (F.app (F.rAdj.app X)) X :=
ofHomAux (HomAux.counit F hF X)

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
  -- Suppose we have f : X → Y where X and Y are Objects of C and the context is cased.
  -- If Y is rAdj, then f must be either restrict or a variable to be almostNormal
  -- If Y is not rAdj then f is almostNormal if every rAdj functor contained in
    f is contained in a variable in F or X or Y.
  -- A term is normal if every subterm (define properly) is almostNormal
 -/

end Hom

def Context.varCases (Γ : Context) : {C : Cat} → {X Y : Obj C} → (v : Γ.HomVar X Y) →
  Hom Γ.cases X Y
| _, X, Obj.rAdjApp F Y, v => Hom.restrict F _ _


mutual

def HomAuxCaseContext : {C : Cat} → {X Y : Obj C} → (f : HomAux Γ X Y) → HomAux Γ.cases X Y
| _, _, _, HomAux.mapVar v f => HomAux.mapVar v (HomAuxCaseContext f)
| _, _, _, HomAux.mapRAdj F f => HomAux.mapRAdj F (HomAuxCaseContext f)
| _, _, _, @HomAux.var _ C X Y v => HomAux.var ⟨_, _, _, _, v⟩

end
