inductive Cat
| mk : Nat → Cat

open Sum

mutual

inductive Obj : Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| corepr {C : Cat} (F : Presheaf C) : Obj C
| app {C D : Cat} (v : Nat) (X : Obj C) : Obj D

inductive Presheaf : Cat → Type where
| compVar {C D : Cat} (F : Presheaf C) (v : Nat) : Presheaf D
| var {C : Cat} (v : Nat) : Presheaf C
| hom {C : Cat} (X : Obj C) : Presheaf C

end

open Presheaf Obj

structure ContextAux : Type 1 :=
( elem {C : Cat} (F : Presheaf C) (X : Obj C) : Type )
( isCorepr {C : Cat} : Presheaf C → Prop )

variable (Γ : ContextAux)

inductive ValidObjFunc (Γ : ContextAux) : {C : Cat} → (Presheaf C ⊕ Obj C) → Prop
| var (C : Cat) (n : Nat) : ValidObjFunc Γ (Sum.inr (Obj.var C n))
| corepr {C : Cat} (F : Presheaf C) (h : Γ.isCorepr F) : ValidObjFunc Γ (Sum.inr (Obj.corepr F))
| app {C D : Cat} (v : Nat) (X : Obj C) : ValidObjFunc Γ (Sum.inr X) →
  ValidObjFunc Γ (Sum.inr (Obj.app v X : Obj D))
| compVar {C D : Cat} (F : Presheaf C) (v : Nat) : ValidObjFunc Γ (Sum.inl F) →
  ValidObjFunc Γ (Sum.inl (compVar F v))
| Pvar {C : Cat} (v : Nat) : ValidObjFunc Γ (Sum.inl (Presheaf.var v : Presheaf C))
| hom {C : Cat} (X : Obj C) : ValidObjFunc Γ (Sum.inr X) →
  ValidObjFunc Γ (Sum.inl (Presheaf.hom X))

def ContextAux.ValidObj (Γ : ContextAux) {C : Cat} (X : Obj C) : Prop :=
ValidObjFunc Γ (Sum.inr X)

def ContextAux.ValidPresheaf (Γ : ContextAux) {C : Cat} (F : Presheaf C) : Prop :=
ValidObjFunc Γ (Sum.inl F)

def ContextAux.Good (Γ : ContextAux) : Prop :=
∀ {C : Cat} (F : Presheaf C), Γ.isCorepr F → Γ.ValidPresheaf F ∧
∀ {C : Cat} (F : Presheaf C) (X : Obj C) (x : Γ.elem F X),
  Γ.ValidPresheaf F ∧ Γ.ValidObj X

def Context : Type 1 :=
{ Γ : ContextAux // Γ.Good }

def Context.ValidObj (Γ : Context) {C : Cat} (X : Obj C) : Prop :=
Γ.1.ValidObj X

@[instance] axiom Context.ValidObj.Decidable (Γ : Context) {C : Cat} (X : Obj C) :
  Decidable (Γ.ValidObj X)

def Context.ValidPresheaf (Γ : Context) {C : Cat} (F : Presheaf C) : Prop :=
Γ.1.ValidPresheaf F

def Context.elem (Γ : Context) {C : Cat} (F : Presheaf C) (X : Obj C) : Type :=
Γ.1.elem F X

def Context.isCorepr (Γ : Context) {C : Cat} : Presheaf C → Prop :=
Γ.1.isCorepr

@[instance] axiom Context.isCorepr.Decidable (Γ : Context) {C : Cat} (F : Presheaf C) :
  Decidable (Γ.isCorepr F)

structure Context.Hom (Γ₁ Γ₂ : Context) :=
( elem {C : Cat} {F : Presheaf C} {X : Obj C} : Γ₁.elem F X → Γ₂.elem F X )
( isCorepr {C : Cat} {F : Presheaf C} : Γ₁.isCorepr F → Γ₂.isCorepr F )

def Context.id (Γ₁ : Context) : Hom Γ₁ Γ₁ :=
⟨λ x => x, λ x => x⟩

def Context.Hom.comp {Γ₁ Γ₂ Γ₃ : Context} (f : Γ₁.Hom Γ₂) (g : Γ₂.Hom Γ₃) : Γ₁.Hom Γ₃ :=
⟨λ x => g.elem (f.elem x), λ x => g.isCorepr (f.isCorepr x)⟩

structure Context.step (Γ₁ Γ₂ : Context) : Type :=
( elem {C : Cat} {F : Presheaf C} {X : Obj C} : Γ₁.elem F X → Γ₂.elem F X )
( elem_inv {C : Cat} {F : Presheaf C} {X : Obj C} : Γ₂.elem F X → Γ₁.elem F X )
( elem_left_inv {C : Cat} {F : Presheaf C} {X : Obj C} (x : Γ₁.elem F X) : elem_inv (elem x) = x )
( elem_right_inv {C : Cat} {F : Presheaf C} {X : Obj C} (x : Γ₂.elem F X) : elem (elem_inv x) = x )
( isCorepr {C : Cat} {F : Presheaf C} : Γ₂.isCorepr F → Γ₁.ValidPresheaf F )

inductive Elem (Γ : Context) : {C : Cat} → (F : Presheaf C) → (X : Obj C) → Type
| var {C : Cat} {F : Presheaf C} {X : Obj C} (x : Γ.elem F X) : Elem Γ F X
| id {C : Cat} (X : Obj C) : Elem Γ (hom X) X
| comp {C : Cat} {X Y Z : Obj C} (f : Elem Γ (hom X) Y) (g : Elem Γ (hom Y) Z) :
  Elem Γ (hom X) Z
| app {C : Cat} {X Y : Obj C} (F : Presheaf C) (f : Elem Γ (hom X) Y) (x : Elem Γ F X) :
  Elem Γ F Y
| mapVar (C D : Cat) (v : Nat) {X Y : Obj C} (f : Elem Γ (hom X) Y) :
  Elem Γ (hom (@Obj.app C D v X)) (Obj.app v X)
| extend {C : Cat} (F : Presheaf C) (h : Γ.isCorepr F) {X : Obj C}
  (f : Elem Γ F X) : Elem Γ (hom (corepr F)) X
| unit {C : Cat} (F : Presheaf C) (h : Γ.isCorepr F) : Elem Γ F (corepr F)

def Elem.mapContext {Γ₁ Γ₂ : Context} (h : Γ₁.Hom Γ₂) : {C : Cat} → {F : Presheaf C} → {X : Obj C} →
  Elem Γ₁ F X → Elem Γ₂ F X
| _, _, _, Elem.var x => Elem.var (h.elem x)
| _, _, _, Elem.id X => Elem.id X
| _, _, _, Elem.comp f g => Elem.comp (mapContext h f) (mapContext h g)
| _, _, _, Elem.app F f x => Elem.app F (mapContext h f) (mapContext h x)
| _, _, _, Elem.mapVar C D v f => Elem.mapVar C D v (mapContext h f)
| _, _, _, Elem.extend F hC f => Elem.extend F (h.isCorepr hC) (mapContext h f)
| _, _, _, Elem.unit F hC => Elem.unit F (h.isCorepr hC)

structure ActualPresheaf (Γ : Context) (C : Cat) : Type 1 :=
( obj : (X : Obj C) → Γ.ValidObj X → Type )
( map {X Y : Obj C} (hX : Γ.ValidObj X) (hY : Γ.ValidObj Y)
    (f : Elem Γ (hom X) Y) : obj X hX → obj Y hY )

@[simp] def Presheaf.toActualPresheaf (Γ : Context) {C : Cat} (F : Presheaf C) : ActualPresheaf Γ C :=
{ obj := λ X hX => Elem Γ F X,
  map := λ hX hY f x => Elem.app F f x }

@[simp] def yonedaObj {Γ : Context} {C : Cat} (X : Obj C) (hX : Γ.ValidObj X) : ActualPresheaf Γ C :=
{ obj := λ Y hY => Elem Γ (hom X) Y,
  map := λ hY hZ f g => Elem.comp g f }

@[simp] def liftVar {Γ : Context} {C D : Cat} (v : Nat) (F : ActualPresheaf Γ C) :
  ActualPresheaf Γ D :=
{ obj := λ X hX => Σ (Y : Obj C), Elem Γ (hom (Obj.app v Y : Obj D)) X,
  map := λ hX hY f x => ⟨_, Elem.app _ f x.2⟩ }

@[simp] def natTrans {Γ : Context} {C : Cat} (F G : ActualPresheaf Γ C) :=
(X : Obj C) → (hX : Γ.ValidObj X) → G.obj X hX → F.obj X hX

@[simp] noncomputable def toActualPresheafObj {Γ₁ Γ₂ : Context} (hΓ : Γ₁.step Γ₂) :
  {C : Cat} → (X : Obj C) → (hX : Γ₂.ValidObj X) → ActualPresheaf Γ₁ C
| _, Obj.var C n, _ => yonedaObj (Obj.var C n) (by constructor)
| _, Obj.corepr F, _ =>
  if h : Γ₁.isCorepr F
  then yonedaObj (Obj.corepr F) (by constructor; assumption)
  else F.toActualPresheaf _
| _, Obj.app v X, h => liftVar v (toActualPresheafObj hΓ X (by cases h; assumption))

noncomputable def toActualPresheafHom {Γ₁ Γ₂ : Context} (hΓ : Γ₁.step Γ₂) :
  {C : Cat} → {X Y : Obj C} → (hX : Γ₂.ValidObj X) → (hY : Γ₂.ValidObj Y) →
  Elem Γ₂ (hom X) Y →
  natTrans (toActualPresheafObj hΓ X hX) (toActualPresheafObj hΓ Y hY)
| _, _, _, hX, hY, Elem.var x, Z, hZ, g =>
  by simp [toActualPresheafObj] at g ⊢

| _, _, _, _, _, _, _, _, _ => sorry

