inductive Cat :=
| var (n : Nat) : Cat
deriving DecidableEq

inductive ObjKind : Type
| rAdj : ObjKind
| other : ObjKind
deriving DecidableEq

open ObjKind

mutual

inductive ObjAux : ObjKind → Cat → Type where
| var (C : Cat) (n : Nat) : ObjAux other C
| varApp {C D : Cat} (v : Nat) {b : ObjKind} (X : ObjAux b C) : ObjAux other D
| rAdjApp {C D : Cat} (F : Func C D) {b : ObjKind} (X : ObjAux b D) : ObjAux b C

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| compVar {C D E : Cat} (F : Func C D) (v : Nat) : Func C E
| compRAdj {C D E : Cat} (F : Func C D) (G : Func E D) : Func C E

end

def Obj (C : Cat) : Type := Σ b : ObjKind, ObjAux b C

noncomputable def Func.compAux {D E : Cat} (G : Func D E) : (C : Cat) → (F : Func C D) → Func C E :=
@Func.recOn (λ _ _ _ => Unit) (λ D E G => (C : Cat) → (F : Func C D) → Func C E)
  D E G
  (λ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ _ _ _ => ())
  (λ _ _ F => F)
  (λ D v ih C F => compVar (ih _ F) v)
  (λ F G ih _ C H => compRAdj (ih _ H) G)

noncomputable def Func.comp {C D E : Cat} (F : Func C D) (G : Func D E) : Func C E :=
Func.compAux G _ F

noncomputable def Func.app {C D : Cat} (F : Func C D) : (X : Obj C) → Obj D :=
@Func.recOn (λ _ _ _ => Unit) (λ C D _ => Obj C → Obj D)
  C D F
  (λ _ _ => ())
  (λ _ _ _ _ => ())
  (λ _ _ _ _ _ => ())
  (λ _ X => X)
  (λ F v ih X => ⟨_, ObjAux.varApp v (ih X).2⟩)
  (λ F G ih _ X => ⟨_, ObjAux.rAdjApp G (ih X).2⟩)

theorem Func.idApp {C : Cat} (X : Obj C) : (Func.id C).app X = X := rfl

theorem Func.compVarApp {C D E : Cat} (F : Func C D) (v : Nat) (X : Obj C) :
  (@Func.compVar C D E F v).app X = ⟨_, ObjAux.varApp v (F.app X).2⟩ := rfl

theorem Func.compRAdjApp {C D E : Cat} (F : Func C D) (G : Func E D) (X : Obj C) :
  (Func.compRAdj F G).app X = ⟨_, ObjAux.rAdjApp G (F.app X).2⟩ := rfl

def Func.var (C D : Cat) (v : Nat) : Func C D :=
Func.compVar (Func.id _) v

def Func.rAdj {C D : Cat} (F : Func D C) : Func C D :=
Func.compRAdj (Func.id _) F

noncomputable def ObjAux.cases : {C : Cat} → {bX bY : ObjKind} →
  (X : ObjAux bX C) → (Y : ObjAux bY C) → Σ D : Cat, Obj D × ObjAux other D
| C, _, _, X, ObjAux.rAdjApp F Y => cases (F.app ⟨_, X⟩).2 Y
| C, _, ObjKind.other, X,      Y => ⟨C, ⟨_, X⟩, Y⟩

noncomputable def Obj.cases {C : Cat} (X Y : Obj C) : Σ D : Cat, Obj D × ObjAux other D :=
ObjAux.cases X.2 Y.2

structure HomData : Type :=
( isVarApp : Option (Cat × Nat) )
( isCounit : Option (Σ (C D : Cat), Func C D) )

inductive rAdjChain : (C D : Cat) → Type
| single : {C D : Cat} → Func C D → rAdjChain D C
|

mutual

inductive HomAux₁ : {C : Cat} → (X Y : Obj C) → HomData → Type where
| mapVar {C D : Cat} {X Y : Obj C} {o : HomData} (v : Nat) (f : HomComp X Y o) :
  HomAux₁ ((Func.var C D v).app X) ((Func.var C D v).app Y) ⟨some (C, v), none⟩
| varCases {C : Cat} (X Y : Obj C) (v : Nat) :
  HomAux₁ (X.cases Y).2.1 ⟨other, (X.cases Y).2.2⟩ ⟨none, none⟩
| counit {C D : Cat} (F : Func C D) (X : ObjAux other D) :
  HomAux₁ (F.app (F.rAdj.app ⟨_, X⟩)) ⟨_, X⟩
  ⟨none, some ⟨_, _, F⟩⟩
| restrict {C D : Cat} (F : Func C D) {X : Obj C} {Y : Obj D} {o : HomData} :
  HomAux (F.app X) Y o → HomAux₁ X ⟨_, ObjAux.rAdjApp F Y.2⟩ ⟨none, none⟩

-- Need to think a lot about composition of Adjoints.

inductive HomComp : {C : Cat} → (X Y : Obj C) → HomData → Type where
| ofHom₁ {C : Cat} {X Y : Obj C} {o : HomData} : HomAux₁ X Y o → HomComp X Y o
| comp' {C : Cat} {X Y : Obj C} {Z : ObjAux other C} {o₁ o₂ : HomData}
  (h : o₁.isVarApp ≠ o₂.isVarApp ∨ o₁.isVarApp = none)
  (f : HomAux₁ X Y o₁) (g : HomComp Y ⟨_, Z⟩ o₂) : HomComp X ⟨_, Z⟩ o₁

inductive HomAux : {C : Cat} → (X Y : Obj C) → HomData → Type where
| ofComp {C : Cat} {X Y : Obj C} {o : HomData} : HomComp X Y o → HomAux X Y o
| id {C : Cat} (X : ObjAux other C) : HomAux ⟨_, X⟩ ⟨_, X⟩ ⟨none, none⟩

end

def Hom₁.isMapVar : (C D : Cat) → (v : Nat) → {X Y : Obj D} → Hom₁ X Y → Prop
| C, _, w, _, _, @Hom₁.mapVar C' _ _ _ v _ => C = C' ∧ w = v
| _, _, _, _, _, Hom₁.varCases _ _ _  => False
| _, _, _, _, _, Hom₁.counit _ _ => False
| _, _, _, _, _, Hom₁.restrict _ _ => False

def HomComp.headIsMapVar (C D : Cat) (v : Nat) : {X Y : Obj D} → HomComp X Y → Prop
| _, _, ofHom₁ f => Hom₁.isMapVar C D v f
| _, _, comp' f g => Hom₁.isMapVar C D v f

def HomComp.comp : {C : Cat} → {X Y Z : Obj C} →
  HomComp X Y → HomComp Y Z → HomComp X Z
| _, _, _, _, HomComp.id _, g => g
| _, _, _, _, HomComp.comp' f g hfg, HomComp.id _ => HomComp.comp' f g hfg
| _, _, _, _, HomComp.comp' f g hfg, HomComp.comp' h i hhi =>
  HomComp.comp' f (comp g (HomComp.comp' h i hhi)) _

namespace Hom

variable {C D : Cat}

section defs

noncomputable def ofHom₁ : {X Y : Obj C} → (f : Hom₁ X Y) → Hom X Y
| _, _, Hom₁.mapVar v f => Hom.ofComp (HomComp.comp' (Hom₁.mapVar v f) (HomComp.id _))
| _, _, Hom₁.varCases X Y v => Hom.ofComp (HomComp.comp' (Hom₁.varCases X Y v) (HomComp.id _))
| _, _, Hom₁.counit F X => Hom.ofComp (HomComp.comp' (Hom₁.counit F X) (HomComp.id _))

noncomputable def varCases (X Y : Obj C) (v : Nat) : Hom (X.cases Y).2.1 ⟨_, (X.cases Y).2.2⟩ :=
ofHom₁ (Hom₁.varCases X Y v)

noncomputable def comp : {C : Cat} → {X Y Z : Obj C} →
  Hom X Y → Hom Y Z → Hom X Z
| _, _, _, _, Hom.ofComp f, Hom.ofComp g => Hom.ofComp (f.comp g)
| _, _, _, _, Hom.ofComp f, h => Hom.HomComp.comp f (comp g h)

noncomputable def mapAux : {C D : Cat} → (F : Func C D) → {X Y : Obj C} →
  (f : Hom₁ X Y) → Hom₁ (F.app X) (F.app Y)
| _, _, Func.id _,           _, _, f => f
| _, _, (Func.compVar F v),  _, _, f => Hom₁.mapVar v (mapAux F f)
| _, _, (Func.compRAdj F G), _, _, f => Hom₁.mapRAdj G (mapAux F f)

noncomputable def map {C D : Cat} (F : Func C D) : {X Y : Obj C} →
  (f : Hom X Y) → Hom (F.app X) (F.app Y)
| _, _, Hom.id _ => Hom.id _
| _, _, Hom.comp' f g => Hom.comp' (mapAux F f) (map F g)

noncomputable def restrict {C D : Cat} (F : Func C D)
  {X : Obj C} {Y : Obj D}
  (f : Hom (F.app X) Y) : Hom X (Obj.rAdjApp F Y) :=
ofHom₁ (Hom₁.restrict F f)

noncomputable def counit {C D : Cat} (F : Func C D) (X : Obj D) :
  Hom (F.app (F.rAdj.app X)) X :=
ofHom₁ (Hom₁.counit F X)

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
