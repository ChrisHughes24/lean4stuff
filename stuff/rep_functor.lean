inductive Cat :=
| Set : Cat
| var (n : Nat) : Cat

open Sum

mutual

inductive Obj : Cat → Type where
| var (C : Cat) (n : Nat) : Obj C
| corepr {C : Cat} (F : Func C Cat.Set) : Obj C
| app' {C D : Cat} (F : Func' C D) (X : Obj C) : Obj D

inductive Func' : (C : Cat) → Cat → Type where
| var (C D : Cat) (n : Nat) : Func' C D
| hom (C : Cat) (X : Obj C) : Func' C Cat.Set -- X is the domain
| prod {C : Cat} (F G : Func C Cat.Set) : Func' C Cat.Set

inductive Func : Cat → Cat → Type where
| id (C : Cat) : Func C C
| comp' {C D E : Cat} (F : Func' C D) (G : Func D E) : Func C E

end

def Func.comp : {C D E : Cat} → (F : Func C D) → (G : Func D E) → Func C E
| _, _, _, Func.id _,      G => G
| _, _, _, Func.comp' F G, H => Func.comp' F (comp G H)

def Func.app : {C D : Cat} → (F : Func C D) → Obj C → Obj D
| _, _, Func.id _,      X => X
| _, _, Func.comp' F G, X => app G (Obj.app' F X)

def Func.hom {C : Cat} (X : Obj C) : Func C Cat.Set :=
Func.comp' (Func'.hom C X) (Func.id _)

def Func.var (C D : Cat) (n : Nat) : Func C D :=
Func.comp' (Func'.var C D n) (Func.id _)

def Func.prod {C : Cat} (F G : Func C Cat.Set) : Func C Cat.Set :=
Func.comp' (Func'.prod F G) (Func.id _)

open Func Obj

inductive Elem : (X : Obj Cat.Set) → Type
| var (X : Obj Cat.Set) (n : Nat) : Elem X
| id {C : Cat} (X : Obj C) : Elem ((Func.hom X).app X)
| comp {C : Cat} {X Y Z : Obj C}
  (f : Elem ((hom X).app Y))
  (g : Elem ((hom Y).app Z)) : Elem ((hom X).app Z)
| app {X Y : Obj Cat.Set} (f : Elem ((hom X).app Y)) (x : Elem X) : Elem Y
| map {C D : Cat} (F : Func C D) {X Y : Obj C} (f : Elem ((hom X).app Y)) :
  Elem (app (hom (app F X)) (app F Y))
| extend {C : Cat} (F : Func C Cat.Set) {X : Obj C} :
  Elem ((app (hom (app F X)) (app (hom (corepr F)) X)))
| unit {C : Cat} (F : Func C Cat.Set) : Elem (app F (corepr F))
| prod_mk {C : Cat} (F G : Func C Cat.Set) (X : Obj C) :
  Elem (app (hom (app F X)) (app (hom (app G X)) (app (prod F G) X)))
| prod_fst {C : Cat} (F G : Func C Cat.Set) (X : Obj C) :
  Elem (app (hom (app (prod F G) X)) (app F X))
| prod_snd {C : Cat} (F G : Func C Cat.Set) (X : Obj C) :
  Elem (app (hom (app (prod F G) X)) (app G X))

inductive subterm :
  (t₁ t₂ : (Σ (C : Cat), Obj C) ⊕ (Σ (C D : Cat), Func' C D) ⊕ (Σ (C D : Cat), Func C D)) → Prop
| corepr {C : Cat} (F : Func C Cat.Set) : subterm

def CatContext : Type := Cat → Bool

def ObjContext (Γ_c : CatContext) : Type :=
(C : Cat) → (Γ_c C) → Nat → Bool

mutual

inductive ReprContext ()

#exit