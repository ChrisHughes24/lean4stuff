import Mathlib.Data.List.AList

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

attribute [local simp] eval normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars List.disjoint max_add_add_right max_mul_mul_left

@[simp]
def E.normSize : E → ℕ
  | lit _ => 0
  | var _ => 0
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1

/-- Normalizes the expression at the same time as assign all variables in
`va` to the literal boolean given by `va` -/
def E.normalize (va : AList (fun _ : ℕ => Bool)) :
    (e : E) → { e' : E // e'.normalized ∧
        (∀ f, e'.eval f = e.eval
          (fun w => (va.lookup w).elim (f w) (fun b => b))) ∧
        ∀ (v : ℕ) (b : Bool), v ∈ vars e' → va.lookup v ≠ some b }
  | lit b => ⟨lit b, by simp⟩
  | var v =>
    match h : va.lookup v with
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
    match h : va.lookup v with
    | none =>
      have ⟨t', ht₁, ht₂, ht₃⟩ := E.normalize (va.insert v true) t
      have ⟨e', he₁, he₂, he₃⟩ := E.normalize (va.insert v false) e
      if hte' : t' = e'
      then by
        subst hte'
        refine ⟨t', ht₁, ?_, ?_⟩
        · intro f
          cases hfv : f v
          · simp only [he₂, Option.elim, ne_eq, eval, h, hfv, cond_false]
            congr
            ext w
            by_cases hwv : w = v
            · subst w
              simp [hfv, h]
            · simp [hwv]
          · simp only [ht₂, Option.elim, ne_eq, eval, h, hfv, cond_false]
            congr
            ext w
            by_cases hwv : w = v
            · subst w
              simp [hfv, h]
            · simp [hwv]
        · intro w b
          by_cases hwv : w = v
          · subst v
            simp [h]
          · have := ht₃ w b
            have := he₃ w b
            aesop
      else ⟨.ite (var v) t' e', by
        refine ⟨?_, ?_, ?_⟩
        · suffices : v ∉ vars t' ∧ v ∉ vars e'
          · aesop
          refine ⟨?_, ?_⟩
          · intro h
            have := ht₃ v true h
            simp at this
          · intro h
            have := he₃ v false h
            simp at this
        · intro f
          simp [he₂, ht₂, ht₁]
          cases hfv : f v
          · simp only [ne_eq, cond_false, h]
            congr
            ext w
            by_cases hwv : w = v
            · subst w
              simp [hfv, h]
            · simp [hwv]
          · simp only [ne_eq, cond_true, h]
            congr
            ext w
            by_cases hwv : w = v
            · subst w
              simp [hfv, h]
            · simp [hwv]
        · simp only [vars, List.mem_append, List.mem_singleton]
          intro w b
          by_cases hwv : w = v
          · subst v
            simp [h]
          · have := ht₃ w b
            have := he₃ w b
            aesop⟩
    | some true =>
      have ⟨t', ht'⟩ := E.normalize va t
      ⟨t', by aesop⟩
    | some false =>
      have ⟨e', he'⟩ := E.normalize va e
      ⟨e', by aesop⟩
  termination_by E.normalize e => e.normSize

def IfNormalization : Type := { Z : E → E // ∀ e, (Z e).normalized ∧ ∀ f, (Z e).eval f = e.eval f }

example : IfNormalization :=
  ⟨fun e => (E.normalize ∅ e).1, by
    intro e
    refine ⟨(E.normalize ∅ e).2.1, ?_⟩
    intro f
    rw [(E.normalize ∅ e).2.2.1 f]
    simp⟩
