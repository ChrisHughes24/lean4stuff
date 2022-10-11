variable (Typ : Type)

inductive LTyp : Type
| ofTyp : Typ → LTyp
| arrow : LTyp → LTyp → LTyp

inductive Context : Nat → Type
| empty : Context (0 : Nat)
| cons : Context n → LTyp Typ → Context (n+1)

inductive Fin2 : Nat → Type
| last (n : Nat) : Fin2 (n+1)
| raise {n : Nat} : Fin2 n → Fin2 (n+1)

variable {Typ}

/-- Oth thing in the context is furthest left -/
def Context.nth : {n : Nat} → Fin2 n → Context Typ n → LTyp Typ
| _, Fin2.last _, Context.cons _ t => t
| _, Fin2.raise i, Context.cons Γ _ => Context.nth i Γ

variable (Const : LTyp Typ → Type)

inductive Term : {n : Nat} → (Γ : Context Typ n) → LTyp Typ → Type
| ofConst {t : LTyp Typ} : Const t → Term Γ t
| boundVar {n : Nat} {Γ : Context Typ n}
  (i : Fin2 n) : Term Γ (Context.nth i Γ)
| lambda {n : Nat} {Γ : Context Typ n} {t u : LTyp Typ} (e : Term (Γ.cons t) u) :
  Term Γ (t.arrow u)
| app {n : Nat} {Γ : Context Typ n} {t u : LTyp Typ}
  (e : Term Γ (t.arrow u)) (x : Term Γ t) : Term Γ u

def assign_last_var : {n : Nat} → {Γ : Context Typ n} → {t u : LTyp Typ} →
  (e : Term Const (Γ.cons t) u) → (x : Term Const Γ t) → Term Const Γ u
| _, _, _, _, Term.app e x, y =>
  Term.app (assign_last_var e y) (assign_last_var x y)
| n, Γ, t, _, @Term.lambda _ _ _ _ u v e, x =>
  have := assign_last_var e
  Term.lambda _
| _, _, _, _, _, _ => sorry

def assign_var : {n : Nat} → {Γ : Context Typ n} → {t : LTyp Typ} →
  (e : Term Const Γ t) → {i : Fin2 n} → (x : Term Const Γ (Γ.nth i)) → Term Const Γ u
| _, _, _, _, Term.app e x, y =>
  Term.app (assign_last_var e y) (assign_last_var x y)
| n, Γ, t, _, @Term.lambda _ _ _ _ u v e, x =>
  have := assign_last_var e
  Term.lambda _
| _, _, _, _, _, _ => sorry

def beta_reduce : {n : Nat} → {Γ : Context Typ n} → {t : LTyp Typ} →
  (e : Term Γ t) →

-- λ x : X. λ y : Y. y
example :
  let Typ : Type := String
  let Const : LTyp Typ → Type := λ _ => Empty
  let X : LTyp Typ := LTyp.ofTyp "X"
  let Y : LTyp Typ := LTyp.ofTyp "Y"
  Term Const Context.empty (X.arrow (Y.arrow Y)) :=
let Typ : Type := String
let Const : LTyp Typ → Type := λ _ => Empty
let X : LTyp Typ := LTyp.ofTyp "X"
let Y : LTyp Typ := LTyp.ofTyp "Y"
Term.lambda (Term.lambda (Term.boundVar (Fin2.last 1)))

example :
  let Typ : Type := String
  let Const : LTyp Typ → Type := λ _ => Unit
  let X : LTyp Typ := LTyp.ofTyp "X"
  let Y : LTyp Typ := LTyp.ofTyp "Y"
  let Z : LTyp Typ := LTyp.ofTyp "Z"
  let f : Const (X.arrow (Y.arrow Z)) := ()
  let g : Const (X.arrow Y) := ()
  let a : Const X := ()
  Term Const Context.empty
   ((X.arrow (Y.arrow Z)).arrow ((X.arrow Y).arrow (X.arrow Z))) :=
let Typ : Type := String
let Const : LTyp Typ → Type := λ _ => Unit
let X : LTyp Typ := LTyp.ofTyp "X"
let Y : LTyp Typ := LTyp.ofTyp "Y"
let Z : LTyp Typ := LTyp.ofTyp "Z"
let f : Const (X.arrow (Y.arrow Z)) := ()
let g : Const (X.arrow Y) := ()
let a : Const X := ()
Term.lambda (Term.lambda (Term.lambda
  (Term.app
    (Term.app (Term.boundVar (Fin2.raise (Fin2.raise (Fin2.last 0)))) -- f
    (Term.boundVar (Fin2.last 2))) -- a
    (Term.app (Term.boundVar (Fin2.raise (Fin2.last 1)))
      (Term.boundVar (Fin2.last 2))))))



