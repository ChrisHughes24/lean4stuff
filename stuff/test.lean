structure Data : Type :=
( A : Bool )
( B : Bool )
( C : Bool )
( D : Bool )
( E : Bool )
( F : Bool )

def f : Data := ⟨false, false, false, false, false, false⟩

inductive T : Type
| mk1 (d₁ d₂ : Data) : T
| mk2 (d₁ d₂ : Data) : T
| mk3 (d₁ d₂ : Data) : T
| mk4 (d₁ d₂ : Data) : T
| mk5 (d₁ d₂ : Data) : T
| mk6 (d₁ d₂ : Data) : T
| mk7 (d₁ d₂ : Data) : T
| mk8 (d₁ d₂ : Data) : T
| mk9 (d₁ d₂ : Data) : T

def function1 : (x : T) → Nat
| T.mk1 _ _ => 0
| T.mk2 _ _ => 0
| T.mk3 _ _ => 0
| T.mk4 _ _ => 0
| T.mk5 _ _ => 0
| T.mk6 _ _ => 0
| T.mk7 _ _ => 0
| T.mk8 _ _ => 0
| T.mk9 _ _ => 0

def function2 : (x : T) → Nat
| T.mk1 _ _ => _
