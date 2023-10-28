import Mathlib.Data.List.AList

inductive E
| lit : Bool → E
| var : Nat → E
| ite : E → E → E → E
deriving DecidableEq, Repr

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

attribute [local simp] eval normalized hasNestedIf hasConstantIf hasRedundantIf disjoint vars
List.disjoint max_add_add_right max_mul_mul_left Nat.lt_add_one_iff le_add_of_le_right

theorem E.eval_ite_ite (a b c d e : E) (f : ℕ → Bool) :
    (ite (ite a b c) d e).eval f = (ite a (ite b d e) (ite c d e)).eval f := by
  cases h : eval f a <;> simp_all

@[simp] def E.normSize : E → ℕ
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1

/-- Normalizes the expression at the same time as assigning all variables in
`l` to the literal boolean given by `l` -/
def E.normalize (l : AList (fun _ : ℕ => Bool)) :
    (e : E) → { e' : E //
        (∀ f, e'.eval f = e.eval (fun w => (l.lookup w).elim (f w) (fun b => b)))
        ∧ e'.normalized
        ∧ ∀ (v : ℕ), v ∈ vars e' → l.lookup v = none }
  | lit b => ⟨lit b, by simp⟩
  | var v =>
    match h : l.lookup v with
    | none => ⟨var v, by aesop⟩
    | some b => ⟨lit b, by aesop⟩
  | .ite (lit true) t e =>
    have ⟨t', ht'⟩ := E.normalize l t
    ⟨t', by aesop⟩
  | .ite (lit false) t e =>
    have ⟨e', he'⟩ := E.normalize l e
    ⟨e', by aesop⟩
  | .ite (.ite a b c) d e =>
    have ⟨t', ht₁, ht₂⟩ := E.normalize l (.ite a (.ite b d e) (.ite c d e))
    ⟨t', fun f => by rw [ht₁, eval_ite_ite], ht₂⟩
  | .ite (var v) t e =>
    match h : l.lookup v with
    | none =>
      have ⟨t', ht₁, ht₂, ht₃⟩ := E.normalize (l.insert v true) t
      have ⟨e', he₁, he₂, he₃⟩ := E.normalize (l.insert v false) e
      ⟨if t' = e' then t' else .ite (var v) t' e', by
        refine ⟨fun f => ?_, ?_, fun w b => ?_⟩
        · simp only [eval, apply_ite (eval f), ite_eq_iff']
          cases hfv : f v
          · simp (config := {contextual := true}) only [cond_false, h, he₁]
            refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
            { congr
              ext w
              by_cases w = v <;> aesop }
          · simp only [cond_true, h, ht₁]
            refine ⟨fun _ => ?_, fun _ => ?_⟩ <;>
            { congr
              ext w
              by_cases w = v <;> aesop }
        · have := ht₃ v
          have := he₃ v
          aesop
        · have := ht₃ w
          have := he₃ w
          by_cases w = v <;> aesop⟩
    | some b =>
      have ⟨e', he'⟩ := E.normalize l (.ite (lit b) t e)
      ⟨e', by aesop⟩
  termination_by E.normalize e => e.normSize

def IfNormalization : Type := { Z : E → E // ∀ e, (Z e).normalized ∧ ∀ f, (Z e).eval f = e.eval f }

example : IfNormalization :=
  ⟨fun e => (E.normalize ∅ e).1,
   fun e => ⟨(E.normalize ∅ e).2.2.1, fun f => by simp [(E.normalize ∅ e).2.1 f]⟩⟩
