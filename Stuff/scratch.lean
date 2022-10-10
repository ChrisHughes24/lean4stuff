
inductive A :=
| a : A

inductive B : A → Type where
| hom {C : A} (X : B C) : B A.a

inductive C : A → Type where
| id (a : A) : C a

axiom Func.app (a b : A) (F : C a) : (X : B a) → B b

def Func.var {a : A} (v : Nat) : C a :=
C.id

open B C

inductive T : B A.a → Type
| mk {a: A} {X : B a} (f : T (hom X)) :
  T (hom (Func.app a _ C.id X))
