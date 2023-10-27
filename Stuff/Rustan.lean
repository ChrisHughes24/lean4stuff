import Mathlib.Tactic

inductive E
| lit : Bool → E
| var : Nat → E
| ite : E → E → E → E
deriving BEq

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

def E.occs : E → List ℕ
  | lit _ => []
  | var v => List.ofFn (fun i : Fin (v+1) => if i = Fin.last _ then 1 else 0)
  | ite i t e => List.zipWith (· + ·) (List.zipWith (· + ·) i.occs t.occs) e.occs

def E.elimVar (v : ℕ) : E → (E × E)
  | lit b => (lit b, lit b)
  | var w => if v = w then (lit true, lit false) else (var w, var w)
  | ite i t e =>
    let (i₁, i₂) := i.elimVar v
    let (t₁, t₂) := t.elimVar v
    let (e₁, e₂) := e.elimVar v
    (ite i₁ t₁ e₁, ite i₂ t₂ e₂)

theorem E.eval_elimVar_fst (v : ℕ) : ∀ (e : E) (f : ℕ → Bool),
    eval f (e.elimVar v).1 = eval (fun w => if v = w then true else f w) e
  | lit b, _ => by simp [elimVar, eval]
  | var w, f => by
    simp [elimVar, eval]
    split_ifs <;>
    simp_all [eval, beq_iff_eq]
  | ite i t e, f => by
    simp [elimVar, eval]
    simp only [eval_elimVar_fst]

theorem E.eval_elimVar_snd (v : ℕ) : ∀ (e : E) (f : ℕ → Bool),
    eval f (e.elimVar v).2 = eval (fun w => if v = w then false else f w) e
  | lit b, _ => by simp [elimVar, eval]
  | var w, f => by
    simp [elimVar, eval]
    split_ifs <;>
    simp_all [eval, beq_iff_eq]
  | ite i t e, f => by
    simp [elimVar, eval]
    simp only [eval_elimVar_snd]

theorem E.vars_elimVar_fst (v : ℕ) : ∀ (e : E),
    (e.elimVar v).1.vars = e.vars.filter (v ≠ ·)
  | lit _ => by simp [elimVar, vars]
  | var w => by
    simp [elimVar, vars]
    split_ifs <;>
    simp_all [vars, beq_iff_eq, List.filter]
  | ite i t e => by
    simp [elimVar, vars]
    simp only [vars_elimVar_fst, decide_not]

theorem E.vars_elimVar_snd (v : ℕ) : ∀ (e : E),
    (e.elimVar v).2.vars = e.vars.filter (v ≠ ·)
  | lit _ => by simp [elimVar, vars]
  | var w => by
    simp [elimVar, vars]
    split_ifs <;>
    simp_all [vars, beq_iff_eq, List.filter]
  | ite i t e => by
    simp [elimVar, vars]
    simp only [vars_elimVar_snd, decide_not]

def E.disjointLE (v : ℕ) : E → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      (i.vars.filter (· ≤ v)).disjoint t.vars &&
      (i.vars.filter (· ≤ v)).disjoint e.vars &&
      i.disjointLE v && t.disjointLE v && e.disjointLE v

theorem List.disjoint_iff : ∀ {xs ys : List ℕ},
    xs.disjoint ys = (∀ x ∈ xs, x ∉ ys : Bool)
  | [], _=> by simp [List.disjoint]
  | x::xs, ys => by
    simp [List.disjoint, @List.disjoint_iff xs]

theorem E.disjointLE_of_le {v w : ℕ} (h : v ≤ w) :
    ∀ {e : E}, e.disjointLE w → e.disjointLE v
  | lit _ => by simp [disjointLE]
  | var _ => by simp [disjointLE]
  | ite i t e => by
    simp only [disjointLE, List.disjoint_iff, List.mem_filter, decide_eq_true_eq, and_imp,
      Bool.and_eq_true, and_assoc]
    intro h₁ h₂ hi ht he
    exact ⟨fun x hx hxv => h₁ x hx (le_trans hxv h),
            fun x hx hxv => h₂ x hx (le_trans hxv h),
            E.disjointLE_of_le h hi,
            E.disjointLE_of_le h ht,
            E.disjointLE_of_le h he⟩

def E.dedupLE (v : ℕ) : (e : E) → (h : ∀ w < v, e.disjointLE w) →
    { e' : E // e'.eval = e.eval ∧ e'.disjointLE v}
  | lit b, _ => ⟨lit b, by simp [disjointLE, eval]⟩
  | var i, _ => ⟨var i, by simp [disjointLE, eval]⟩
  | ite i t e, h =>
    let i' := i.elimVar v
    let t' := t.elimVar v
    let e' := e.elimVar v
    ⟨ite (var v) (ite i'.1 t'.1 e'.1) (ite i'.2 t'.2 e'.2), by
      ext f
      simp [eval, eval_elimVar_fst, eval_elimVar_snd]
      by_cases hfv : f v = true
      · simp [hfv]
        congr <;>
        ext <;> split_ifs <;> simp_all
      · simp [eq_false_of_ne_true hfv]
        congr <;>
        ext <;> split_ifs <;> simp_all, by
    simp [disjointLE, E.vars_elimVar_snd, E.disjoint, E.vars,
      E.vars_elimVar_fst, List.disjoint_iff, List.mem_filter] at h ⊢


    ⟩


def IfNormalization : Type := { Z : E → E // ∀ e, (Z e).normalized ∧ ∀ f, (Z e).eval f = e.eval f }

example : IfNormalization := sorry
