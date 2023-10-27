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

theorem E.disjointLE_elimVar_fst {v : ℕ} :
    ∀ (e : E), (∀ w < v, disjointLE w e) ↔ disjointLE v (e.elimVar v).1
  | lit _ => by simp [elimVar, disjointLE]
  | var w => by
    simp [elimVar, disjointLE]
    split_ifs
    · simp [disjointLE]
    · simp [disjointLE]
  | ite i t e => by
    simp only [disjointLE, Bool.and_eq_true, forall_and,
      vars_elimVar_fst, vars_elimVar_snd,
      i.disjointLE_elimVar_fst,
      t.disjointLE_elimVar_fst,
      e.disjointLE_elimVar_fst,
      ← and_assoc, and_congr_left_iff]
    intros _ _ _
    simp [List.disjoint_iff, List.mem_filter, decide_eq_true]
    refine and_congr ?_ ?_
    . refine ⟨fun h x hxi hxv hvx hxt =>
        (h x (lt_of_le_of_ne hxv (Ne.symm hvx)) x hxi (le_refl x) hxt).elim,
        fun h x hxv y hyi hyx hyt => ne_of_lt (lt_of_le_of_lt hyx hxv)
          (Eq.symm (h y hyi (le_trans hyx (le_of_lt hxv))
          (Ne.symm (ne_of_lt (lt_of_le_of_lt hyx hxv))) hyt))⟩
    · refine ⟨fun h x hxi hxv hvx hxt =>
        (h x (lt_of_le_of_ne hxv (Ne.symm hvx)) x hxi (le_refl x) hxt).elim,
        fun h x hxv y hyi hyx hyt => ne_of_lt (lt_of_le_of_lt hyx hxv)
          (Eq.symm (h y hyi (le_trans hyx (le_of_lt hxv))
          (Ne.symm (ne_of_lt (lt_of_le_of_lt hyx hxv))) hyt))⟩

theorem E.disjointLE_elimVar_snd {v : ℕ} :
    ∀ (e : E), (∀ w < v, disjointLE w e) ↔ disjointLE v (e.elimVar v).2
  | lit _ => by simp [elimVar, disjointLE]
  | var w => by
    simp [elimVar, disjointLE]
    split_ifs
    · simp [disjointLE]
    · simp [disjointLE]
  | ite i t e => by
    simp only [disjointLE, Bool.and_eq_true, forall_and,
      vars_elimVar_snd, vars_elimVar_snd,
      i.disjointLE_elimVar_snd,
      t.disjointLE_elimVar_snd,
      e.disjointLE_elimVar_snd,
      ← and_assoc, and_congr_left_iff]
    intros _ _ _
    simp [List.disjoint_iff, List.mem_filter, decide_eq_true]
    refine and_congr ?_ ?_
    . refine ⟨fun h x hxi hxv hvx hxt =>
        (h x (lt_of_le_of_ne hxv (Ne.symm hvx)) x hxi (le_refl x) hxt).elim,
        fun h x hxv y hyi hyx hyt => ne_of_lt (lt_of_le_of_lt hyx hxv)
          (Eq.symm (h y hyi (le_trans hyx (le_of_lt hxv))
          (Ne.symm (ne_of_lt (lt_of_le_of_lt hyx hxv))) hyt))⟩
    · refine ⟨fun h x hxi hxv hvx hxt =>
        (h x (lt_of_le_of_ne hxv (Ne.symm hvx)) x hxi (le_refl x) hxt).elim,
        fun h x hxv y hyi hyx hyt => ne_of_lt (lt_of_le_of_lt hyx hxv)
          (Eq.symm (h y hyi (le_trans hyx (le_of_lt hxv))
          (Ne.symm (ne_of_lt (lt_of_le_of_lt hyx hxv))) hyt))⟩

@[simp]
theorem E.hasNestedIf_elimVar_fst (v : ℕ) :(e : E) →
    hasNestedIf (elimVar v e).1 = hasNestedIf e
  | lit _ => by simp [elimVar, hasNestedIf]
  | var _ => by
    simp [elimVar, hasNestedIf]
    split_ifs <;> simp [hasNestedIf]
  | .ite (.ite _ _ _) _ _ => by
    simp [hasNestedIf, elimVar]
  | .ite (lit _) t e => by
    simp [hasNestedIf, elimVar, t.hasNestedIf_elimVar_fst,
      e.hasNestedIf_elimVar_fst]
  | .ite (var _) t e => by
    simp [hasNestedIf, elimVar, t.hasNestedIf_elimVar_fst,
      e.hasNestedIf_elimVar_fst]
    split_ifs <;>
    simp [hasNestedIf, elimVar, t.hasNestedIf_elimVar_fst,
      e.hasNestedIf_elimVar_fst]

@[simp]
theorem E.hasNestedIf_elimVar_snd (v : ℕ) :(e : E) →
    hasNestedIf (elimVar v e).2 = hasNestedIf e
  | lit _ => by simp [elimVar, hasNestedIf]
  | var _ => by
    simp [elimVar, hasNestedIf]
    split_ifs <;> simp [hasNestedIf]
  | .ite (.ite _ _ _) _ _ => by
    simp [hasNestedIf, elimVar]
  | .ite (lit _) t e => by
    simp [hasNestedIf, elimVar, t.hasNestedIf_elimVar_snd,
      e.hasNestedIf_elimVar_snd]
  | .ite (var _) t e => by
    simp [hasNestedIf, elimVar, t.hasNestedIf_elimVar_snd,
      e.hasNestedIf_elimVar_snd]
    split_ifs <;>
    simp [hasNestedIf, elimVar, t.hasNestedIf_elimVar_snd,
      e.hasNestedIf_elimVar_snd]

def E.dedupLE (v : ℕ) : (e : E) → (h : ∀ w < v, e.disjointLE w) →
    { e' : E // (∀ f, e'.eval f = e.eval f) ∧ e'.disjointLE v ∧
        (∀ w, v < w → w ∈ e'.vars → w ∈ e.vars)
        ∧ (!e.hasNestedIf → !e'.hasNestedIf) }
  | lit b, _ => ⟨lit b, by simp [disjointLE, eval]⟩
  | var i, _ => ⟨var i, by simp [disjointLE, eval]⟩
  | ite i t e, h =>
    let i' := i.elimVar v
    let t' := t.elimVar v
    let e' := e.elimVar v
    ⟨ite (var v) (ite i'.1 t'.1 e'.1) (ite i'.2 t'.2 e'.2), by
      intro f
      simp [eval, eval_elimVar_fst, eval_elimVar_snd]
      by_cases hfv : f v = true
      · simp [hfv]
        congr <;>
        ext <;> split_ifs <;> simp_all
      · simp [eq_false_of_ne_true hfv]
        congr <;>
        ext <;> split_ifs <;> simp_all, by
      simp
        [disjointLE, E.vars_elimVar_snd, E.disjoint, E.vars, and_assoc,
          E.vars_elimVar_fst, List.disjoint_iff, List.mem_filter] at h ⊢
      have h₁ : ∀ (x : ℕ), x ∈ vars i → x ≤ v → ¬v = x → x ∈ vars t → v = x := by
        intro x hxi hxv hvx hxt
        exact ((h x (lt_of_le_of_ne hxv (Ne.symm hvx))).1 x hxi (le_refl x) hxt).elim
      have h₂ : ∀ (x : ℕ), x ∈ vars i → x ≤ v → ¬v = x → x ∈ vars e → v = x := by
        intro x hxi hxv hvx hxe
        exact ((h x (lt_of_le_of_ne hxv (Ne.symm hvx))).2.1 x hxi (le_refl x) hxe).elim
      simp only [← disjointLE_elimVar_fst, ← disjointLE_elimVar_snd]
      simp only [forall_and] at h
      refine ⟨h₁, h₂, ?_, ?_, ?_, h₁, h₂, ?_⟩ <;> tauto, by
      simp [vars, vars_elimVar_fst, vars_elimVar_snd,
        List.mem_filter, or_imp]
      intro w hvw
      simp [ne_of_gt hvw, ne_of_lt hvw]
      tauto, by
      simp [hasNestedIf]
      cases i
      · simp (config := {contextual := true}) [hasNestedIf]
      · simp [hasNestedIf, elimVar]
        split_ifs <;> simp (config := {contextual := true}) [hasNestedIf]
      · simp [hasNestedIf, elimVar]⟩

theorem E.lt_disjointLE_iff_disjointLE_of_not_mem_vars {v : ℕ} : ∀ {e : E},
    (he : v ∉ e.vars) → (∀ w < v, e.disjointLE w) ↔ e.disjointLE v
  | lit _ => by simp [disjointLE]
  | var w => by simp [disjointLE]
  | ite i t e => by
    simp only [disjointLE, vars, List.mem_append, not_or,
      and_imp, Bool.and_eq_true, List.disjoint_iff, List.mem_filter,
      decide_eq_true_iff]
    intro hvi hvt hve
    simp only [forall_and, ← and_assoc,
       ← i.lt_disjointLE_iff_disjointLE_of_not_mem_vars hvi,
       ← t.lt_disjointLE_iff_disjointLE_of_not_mem_vars hvt,
       ← e.lt_disjointLE_iff_disjointLE_of_not_mem_vars hve]
    simp only [and_congr_left_iff]
    intros h₁ h₂ h₃
    refine and_congr ?_ ?_
    . exact ⟨fun h x hxi hxv hxt =>
      h x (lt_of_le_of_ne hxv (by rintro rfl; simp_all))
        x hxi (le_refl _) hxt, fun h x hxv y hyi hyx hyt =>
        h y hyi (le_trans hyx (le_of_lt hxv)) hyt⟩
    . exact ⟨fun h x hxi hxv hxt =>
      h x (lt_of_le_of_ne hxv (by rintro rfl; simp_all))
        x hxi (le_refl _) hxt, fun h x hxv y hyi hyx hyt =>
        h y hyi (le_trans hyx (le_of_lt hxv)) hyt⟩

theorem E.lt_disjointLE_iff_disjointLE_of_not_mem_vars' : ∀ {v : ℕ} {e : E},
    (he : v ∉ e.vars) → (∀ w < v, w ∈ e.vars → e.disjointLE w) ↔ e.disjointLE v
  | v, e, he => by
    conv_rhs => rw [← E.lt_disjointLE_iff_disjointLE_of_not_mem_vars he]
    refine ⟨?_, ?_⟩
    · rintro h w hwv
      by_cases hw : w ∈ e.vars
      · exact h w hwv hw
      · rw [← E.lt_disjointLE_iff_disjointLE_of_not_mem_vars' hw]
        intro x hxw hxe
        exact h x (lt_of_le_of_lt (le_of_lt hxw) hwv) hxe
    · intro h w hwv _
      exact h w hwv

theorem E.disjoint_iff_disjointLE : ∀ {e : E}, e.disjoint ↔ ∀ v, e.disjointLE v
  | lit _ => by simp [disjoint, disjointLE]
  | var _ => by simp [disjoint, disjointLE]
  | E.ite i t e => by
    simp only [disjoint, disjointLE, i.disjoint_iff_disjointLE,
      t.disjoint_iff_disjointLE, e.disjoint_iff_disjointLE,
      List.disjoint_iff, decide_eq_true_iff, Bool.and_eq_true,
      E.vars, List.mem_append, or_assoc, List.mem_filter,
      and_imp, and_assoc]
    refine ⟨?_, ?_⟩
    · intro h v
      tauto
    · intro h
      simp only [← forall_and, and_assoc]
      intro v
      have := h v
      have h₁ := this.1 v
      have h₂ := this.2.1 v
      simp at h₁ h₂
      tauto

def E.dedupAllLE : (v : ℕ) → (e : E) →
    { e' : E // (∀ f, e'.eval f = e.eval f) ∧ e'.disjointLE v ∧
      (∀ w, v < w → w ∈ e'.vars → w ∈ e.vars) ∧
      (!e.hasNestedIf → !e'.hasNestedIf) }
  | 0, e => e.dedupLE 0 (by simp)
  | v+1, e =>
    let e' := E.dedupAllLE v e
    let e'' := @E.dedupLE (v+1) e' (fun w hw =>
      E.disjointLE_of_le (Nat.le_of_lt_succ hw) e'.2.2.1)
    ⟨e''.1, fun _ => by rw [e''.2.1, e'.2.1], e''.2.2.1,
      fun w hvw hwe => by
      have := e''.2.2.2.1 w hvw hwe
      exact e'.2.2.2.1 w (Nat.lt_of_succ_lt hvw) this, by
      intro h
      apply e''.2.2.2.2
      exact e'.2.2.2.2 h⟩

def List.leastGE : (l : List ℕ) → {n : ℕ // ∀ m ∈ l, m ≤ n}
  | [] => ⟨0, by simp⟩
  | a::l =>
    let m := List.leastGE l
    if ham : a ≤ m then ⟨m.1, by
      intro k
      rw [List.mem_cons]
      rintro (rfl | hkl)
      · exact ham
      · exact m.2 _ hkl⟩
    else ⟨a, by
      intro k
      rw [List.mem_cons]
      rintro (rfl | hkl)
      · exact le_refl _
      · exact le_trans (m.2 _ hkl) (le_of_not_ge ham)⟩

def E.dedup (e : E) : { e' : E // (∀ f, e'.eval f = e.eval f) ∧ e'.disjoint ∧
      (!e.hasNestedIf → !e'.hasNestedIf) } :=
  let v := List.leastGE e.vars
  let e' := E.dedupAllLE v e
  ⟨e'.1, e'.2.1, by
    rw [E.disjoint_iff_disjointLE]
    intro w
    by_cases hw : w ≤ v.1
    · exact disjointLE_of_le hw e'.2.2.1
    · have hw : w ∉ e'.1.vars := by
        intro hwe
        have := e'.2.2.2.1 w (lt_of_not_ge hw) hwe
        exact hw (v.2 _ this)
      rw [← E.lt_disjointLE_iff_disjointLE_of_not_mem_vars' hw]
      intro x _ hxe'
      refine disjointLE_of_le ?_ e'.2.2.1
      refine le_of_not_lt ?_
      intro hvx
      have := e'.2.2.2.1 _ hvx hxe'
      have := v.2 _ this
      exact not_le_of_gt hvx this,  e'.2.2.2.2⟩

@[simp]
def E.denestSize : E → ℕ
  | lit _ => 0
  | var _ => 0
  | .ite i t e =>
    2 * E.denestSize i +
      max (E.denestSize t) (E.denestSize e) + 1

def E.denest : (e : E) → { e' : E // (∀ f, e'.eval f = e.eval f) ∧ !e'.hasNestedIf }
  | lit b => ⟨lit b, by simp [eval, hasNestedIf]⟩
  | var i => ⟨var i, by simp [eval, hasNestedIf]⟩
  | .ite (.ite a b c) d e =>
      have : 2 * denestSize a +
          max (2 * denestSize b + max (denestSize d) (denestSize e) + 1)
          (2 * denestSize c + max (denestSize d) (denestSize e) + 1) <
          2 * (2 * denestSize a + max (denestSize b) (denestSize c) + 1) +
          max (denestSize d) (denestSize e) := by
        simp only [denestSize, add_assoc, add_lt_add_iff_left]
        simp only [← add_assoc, max_add_add_right]
        simp only [← two_mul, max_mul_mul_left]
        linarith
      have ⟨t', ht'⟩ := E.denest (.ite a (.ite b d e) (.ite c d e))
      ⟨t', by
        simp [eval, ht'.1, ht'.2, hasNestedIf]
        intro f
        cases eval f a <;> simp⟩
  | .ite (lit true) t e =>
    have : denestSize t < 2 + max (denestSize t) (denestSize e) + 1 :=
      calc denestSize t < max (denestSize t) (denestSize e) + 3 :=
        Nat.lt_succ_of_le (le_add_right (le_max_left _ _))
      _ = _ := by ring
    ⟨E.denest t, by simp [eval, hasNestedIf, (E.denest t).2]⟩
  | .ite (lit false) t e =>
    have : denestSize e < 2 + max (denestSize t) (denestSize e) + 1 :=
      calc denestSize e < max (denestSize t) (denestSize e) + 3 :=
        Nat.lt_succ_of_le (le_add_right (le_max_right _ _))
      _ = _ := by ring
    ⟨E.denest e, by simp [eval, hasNestedIf, (E.denest e).2]⟩
  | .ite (var v) t e =>
    have : denestSize t < 2 + max (denestSize t) (denestSize e) + 1 :=
      calc denestSize t < max (denestSize t) (denestSize e) + 3 :=
        Nat.lt_succ_of_le (le_add_right (le_max_left _ _))
      _ = _ := by ring
    have : denestSize e < 2 + max (denestSize t) (denestSize e) + 1 :=
      calc denestSize e < max (denestSize t) (denestSize e) + 3 :=
        Nat.lt_succ_of_le (le_add_right (le_max_right _ _))
      _ = _ := by ring
    have ⟨t', ht'⟩ := E.denest t
    have ⟨e', he'⟩ := E.denest e
    ⟨.ite (var v) t' e', by
      simp [eval, ht'.1, ht'.2, he'.1, he'.2, hasNestedIf]⟩
  termination_by E.denest e => e.denestSize

def E.deConstRed : (e : E) → { e' : E //
    e.disjoint → !e.hasNestedIf →
    (∀ f, e'.eval f = e.eval f) ∧
    !e'.hasConstantIf ∧
    (!e'.hasNestedIf) ∧
    ( e'.disjoint) ∧
    (!e'.hasRedundantIf) ∧
    e'.vars ⊆ e.vars }
  | lit b => ⟨lit b, by
    simp (config := {contextual := true}) [eval, hasConstantIf, hasRedundantIf]⟩
  | var i => ⟨var i, by
    simp (config := {contextual := true}) [eval, hasConstantIf, hasRedundantIf]⟩
  | .ite (lit true) t e =>
    have ⟨t', ht'⟩ := E.deConstRed t
    ⟨t', by
      simp [Function.funext_iff, disjoint, vars, eval, hasRedundantIf,
        List.disjoint, hasNestedIf, List.subset_def] at *
      tauto
      ⟩
  | .ite (lit false) t e =>
    have ⟨e', he'⟩ := E.deConstRed e
    ⟨e', by
      simp [Function.funext_iff, disjoint, vars, eval, hasRedundantIf,
        List.disjoint, hasNestedIf, List.subset_def] at *
      tauto
      ⟩
  | .ite (var v) t e =>
    have ⟨t', ht'⟩ := E.deConstRed t
    have ⟨e', he'⟩ := E.deConstRed e
    if hte' : t' = e'
    then ⟨t', by
      subst hte'
      simp [Function.funext_iff, disjoint, vars, eval, hasRedundantIf,
        List.disjoint, hasNestedIf, List.subset_def] at *
      aesop
      ⟩
    else
    ⟨.ite (var v) t' e', by
      simp [Function.funext_iff, disjoint, vars, eval, List.subset_def,
        List.disjoint, hasNestedIf, hasConstantIf, hasRedundantIf] at *
      intro _ _ _ _ _ _
      refine ⟨?_, ?_⟩
      · intro f
        cases hf : f v <;> simp_all
      · aesop⟩
  | .ite (.ite a b c) t e =>
    ⟨.ite (.ite a b c) t e, by
      simp [Function.funext_iff, disjoint, vars, eval, List.subset_def,
        List.disjoint, hasNestedIf, hasConstantIf] at *⟩

def E.normalize (e : E) : { e' : E // e'.normalized ∧ ∀ f, e'.eval f = e.eval f } :=
  have ⟨e₁, he₁⟩ := e.denest
  have ⟨e₂, he₂⟩ := e₁.dedup
  have ⟨e₃, he₃⟩ := e₂.deConstRed
  ⟨e₃, by
    refine ⟨?_, ?_⟩
    · simp only [normalized, Bool.and_eq_true]
      aesop
    · intro f
      simp_all⟩

def IfNormalization : Type := { Z : E → E // ∀ e, (Z e).normalized ∧ ∀ f, (Z e).eval f = e.eval f }

example : IfNormalization :=
  ⟨fun e => e.normalize, by
    intro e
    exact ⟨e.normalize.2.1, by
      simpa [Function.funext_iff] using e.normalize.2.2⟩⟩
