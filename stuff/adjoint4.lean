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

noncomputable def ObjAux.cases : {C : Cat} →
  (X : Obj C) → (Y : Obj C) → Σ D : Cat, Obj D × Obj D
| C, X, Obj.rAdjApp F Y => cases (F.app X) Y
| C, X,      Y => ⟨C, X, Y⟩

noncomputable def Obj.cases {C : Cat} (X Y : Obj C) : Σ D : Cat, Obj D × Obj D :=
ObjAux.cases X Y

mutual

-- Hom X (F.rAdj.app Y)
inductive HomRAdj {C D : Cat} : (X : Obj C) → (F : Func C D) → (Y : Obj D) → Type where
| restrict : Hom (F.app X) Y → HomRAdj X F Y

inductive HomAux : {C : Cat} → (X Y : Obj C) → Type where
| mapVar {C D : Cat} {X Y : Obj C} (v : Nat) (f : HomAux X Y) :
  HomAux ((Func.var C D v).app X) ((Func.var C D v).app Y)
| mapRAdj {C D : Cat} {X Y : Obj C} (F : Func D C) (f : HomAux X Y) :
  HomAux (F.rAdj.app X) (F.rAdj.app Y)
| var {C : Cat} {X Y : Obj C} (v : Nat) : HomAux (X.cases Y).2.1 (X.cases Y).2.2
| restrict {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj D} :
  Hom (F.app X) Y → HomAux X (ObjAux.rAdjApp F Y)
| counit {C D : Cat} (F : Func C D) (X : Obj D) :
  HomAux (F.app (F.rAdj.app X)) X

inductive Hom : {C : Cat} → (X Y : Obj C) → Type where
| id {C : Cat} (X : Obj C) : Hom X X
| comp' {C : Cat} {X Y Z : Obj C} (f : HomAux X Y) (g : Hom Y Z) : Hom X Z

end

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
