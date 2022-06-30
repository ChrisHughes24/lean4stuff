
structure Context : Type 1 :=
(CatVar : Type)
(ObjVar : Option CatVar → Type)
(FuncVar : Option CatVar → Option CatVar → Type)

variable (Γ : Context)

def Cat := Option Γ.CatVar

variable {Γ}

def Set : Cat Γ := Option.none

def Var : Γ.CatVar → Cat Γ := Option.some

mutual

inductive Obj : Cat Γ → Type where
| var (C : Cat Γ) (n : Γ.ObjVar C) : Obj C
| corepr {C : Cat Γ} (F : Func C Set) : Obj C
| app' {C D : Cat Γ} (F : Func' C D) (X : Obj C) : Obj D

inductive Func' : Cat Γ → Cat Γ → Type where
| var (C D : Cat Γ) (n : Γ.FuncVar C D) : Func' C D
| hom (C : Cat Γ) (X : Obj C) : Func' C Set -- X is the domain
| prod {C : Cat Γ} (F G : Func C Set) : Func' C Set

inductive Func : Cat Γ → Cat Γ → Type where
| id (C : Cat Γ) : Func C C
| comp' {C D E : Cat Γ} (F : Func' C D) (G : Func D E) : Func C E

end

def Func.comp : {C D E : Cat Γ} → (F : Func C D) → (G : Func D E) → Func C E
| _, _, _, Func.id _,      G => G
| _, _, _, Func.comp' F G, H => Func.comp' F (comp G H)

def Func.app : {C D : Cat Γ} → (F : Func C D) → Obj C → Obj D
| _, _, Func.id _,      X => X
| _, _, Func.comp' F G, X => app G (Obj.app' F X)

def Func.hom {C : Cat Γ} (X : Obj C) : Func C Set :=
Func.comp' (Func'.hom C X) (Func.id _)

def Func.var (C D : Cat Γ) (n : Γ.FuncVar C D) : Func C D :=
Func.comp' (Func'.var C D n) (Func.id _)

def Func.prod {C : Cat Γ} (F G : Func C Set) : Func C Set :=
Func.comp' (Func'.prod F G) (Func.id _)

open Func Obj

inductive Elem : (X : Obj (@Set Γ)) → Type
| var (X : Obj Set) (n : Nat) : Elem X
| id {C : Cat Γ} (X : Obj C) : Elem ((Func.hom X).app X)
| comp {C : Cat Γ} {X Y Z : Obj C}
  (f : Elem ((hom X).app Y))
  (g : Elem ((hom Y).app Z)) : Elem ((hom X).app Z)
| app {X Y : Obj Set} (f : Elem ((hom X).app Y)) (x : Elem X) : Elem Y
| map {C D : Cat Γ} (F : Func C D) {X Y : Obj C} (f : Elem ((hom X).app Y)) :
  Elem (app (hom (app F X)) (app F Y))
| extend {C : Cat Γ} (F : Func C Set) {X : Obj C} :
  Elem ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : Cat Γ} (F : Func C Set) : Elem (app F (corepr F))
| prod_mk {C : Cat Γ} (F G : Func C Set) (X : Obj C) :
  Elem (app (hom (app F X)) (app (hom (app G X)) (app (prod F G) X)))
| prod_fst {C : Cat Γ} (F G : Func C Set) (X : Obj C) :
  Elem (app (hom (app (prod F G) X)) (app F X))
| prod_snd {C : Cat Γ} (F G : Func C Set) (X : Obj C) :
  Elem (app (hom (app (prod F G) X)) (app G X))

/- A context is a set of Categories, a set of object variables,
  a set of functor variables,
  and a set of functors to Set (the corepresentables),
  such that every variable appearing in a functor to Set in the context is
  also in the context. -/

def CatContext : Type := Cat → Prop

def ObjContext (Γ_c : CatContext) : Type :=
(C : Cat) → Γ_c C → Nat → Prop

def CoreprContext (Γ_c : CatContext) (Γ_o : ObjContext Γ_c) : Type :=
(C : Cat) → Γ_c C → (F : Func C Cat.Set) →
  (∀ v, containsCatVar )


/- Longer term plan: Given a context define a relation on terms valid in that context,
  the "equal in all models" relation.

  Given any morphism I would like to prove it has a normal form.
  How? -/

mutual

inductive ReprContext ()

#exit