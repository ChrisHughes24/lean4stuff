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

def Func.hom {C : Cat} (X : Obj C) : Func C Cat.Set :=
Func.comp' (Func'.hom C X) (Func.id _)

open Func Obj

inductive NormElemAux : Obj Cat.Set →  Type
| id {C : Cat} (X : Obj C) : NormElemAux ((Func.hom X).app X)

namespace NormElem

variable {C : Cat}

def comp : {X Y Z : Obj C} →
  (x : NormElemAux ((hom X).app Y)) →
  (y : NormElemAux ((hom Y).app Z)) →
  NormElemAux ((hom X).app Z)
| _, _, _,  (NormElemAux.id _), f => f



end NormElem

inductive T : Nat × Nat → Type
| zero_zero : T (0, 0)

def func : (n m : Nat) → T (n, m) → Nat
| _, _, T.zero_zero => 0
