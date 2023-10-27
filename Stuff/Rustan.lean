import Mathlib.Tactic

inductive E
| lit : Bool → E
| var : Nat → E
| ite : E → E → E → E
deriving DecidableEq

def E.hasNestedIf : E → Bool
| lit _ => false
| var _ => false
| ite (ite _ _ _) _ _ => true
| ite _ t e => t.hasNestedIf || e.hasNestedIf

def E.hasConstantIf : E → Bool
| lit _ => false
| var _ => false
| ite (lit _) _ _ => true
| ite i t e => i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

def E.hasRedundantIf : E → Bool
| lit _ => false
| var _ => false
| ite i t e => t == e || i.hasRedundantIf || t.hasRedundantIf || e.hasRedundantIf

def E.vars : E → List Nat
| lit _ => []
| var i => [i]
| ite i t e => i.vars ++ t.vars ++ e.vars

def List.disjoint : List Nat → List Nat → Bool
| [], _ => true
| (x::xs), ys => x ∉ ys && xs.disjoint ys

def E.disjoint : E → Bool
| lit _ => true
| var _ => true
| ite i t e =>
    i.vars.disjoint t.vars && i.vars.disjoint e.vars && i.disjoint && t.disjoint && e.disjoint

def E.normalized (e : E) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf && !e.hasRedundantIf && e.disjoint

def E.eval (f : Nat → Bool) : E → Bool
| lit b => b
| var i => f i
| ite i t e => bif i.eval f then t.eval f else e.eval f

open E

theorem eval_ite_eq_eval_ite_ite (a b c d e : E) (f : ℕ → Bool) :
    (ite (ite a b c) d e).eval f = (ite a (ite b d e) (ite c d e)).eval f := by
  simp only [eval]
  cases eval f a <;> simp [eval]

attribute [simp] eval normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars List.disjoint

/-- Normalizes the expression at the same time as assign all variables in
`va` to the literal boolean given by `va` -/
def E.normalize (va : Std.RBMap ℕ Bool Ord.compare) :
    (e : E) → { e' : E // e'.normalized ∧
        (∀ f, e'.eval f = e.eval
          (fun w => (va.find? w).elim (f w) (fun b => b))) ∧
        ∀ (v : ℕ) (b : Bool), v ∈ vars e' → va.find? v ≠ some b }
  | lit b => ⟨lit b, by simp⟩
  | var v =>
    match h : va.find? v with
    | none => ⟨var v, by aesop⟩
    | some b => ⟨lit b, by aesop⟩
  | .ite (lit true) t e =>
    have ⟨t', ht'⟩ := E.normalize va t
    ⟨t', by aesop⟩
  | .ite (lit false) t e =>
    have ⟨e', he'⟩ := E.normalize va e
    ⟨e', by aesop⟩
  | .ite (.ite a b c) d e =>
    have ⟨t', ht₁, ht₂, ht₃⟩ := E.normalize va (.ite a (.ite b d e) (.ite c d e))
    ⟨t', ht₁, fun f => by rw [ht₂, eval_ite_eq_eval_ite_ite], ht₃⟩
  | .ite (var v) t e =>
    match h : va.find? v with
    | none =>
      have ⟨t', ht₁, ht₂, ht₃⟩ := E.normalize (va.insert v true) t
      have ⟨e', he₁, he₂, he₃⟩ := E.normalize (va.insert v false) e
      if hte' : t' = e'
      then sorry
      else ⟨.ite (var v) t' e', by
        suffices : v ∉ vars t' ∧ v ∉ vars e'
        · simp [disjoint, vars, eval, List.subset_def, normalized,
            List.disjoint, hasNestedIf, hasConstantIf, hasRedundantIf] at *
          simp_all
        refine ⟨?_, ?_⟩
        · intro h
          have := ht₃ v true h
          simp at this
          sorry
        · intro h
          have := he₃ v false h
          simp at this
          sorry, by
        admit, sorry⟩
    | some true =>
      have ⟨t', ht'⟩ := E.normalize va t
      ⟨t', by aesop⟩
    | some false =>
      have ⟨e', he'⟩ := E.normalize va e
      ⟨e', by aesop⟩

def IfNormalization : Type := { Z : E → E // ∀ e, (Z e).normalized ∧ ∀ f, (Z e).eval f = e.eval f }
