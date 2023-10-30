import Mathlib.Data.Nat.Basic

inductive BDD (level : ℕ) : Type
  | lit : Bool → BDD level
  | ite : (var : ℕ) → BDD level → BDD level → BDD level
deriving Repr, DecidableEq

def normalized : ∀ {level : ℕ}, BDD level → Bool
  | _, .lit _ => true
  | _, .ite _ t e => normalized t ∧ normalized e ∧ t ≠ e

namespace BDD

def eval {level : ℕ} : BDD level → (ℕ → Bool) → Bool
  | lit b, _ => b
  | .ite var t e, f => if f (var + level) then eval t f else eval e f

theorem eval_injective : ∀ {level : ℕ} {b₁ b₂ : BDD level},
    normalized b₁ → normalized b₂ → (∀ (f : ℕ → Bool), eval b₁ f = eval b₂ f) → b₁ = b₂
  | _, .lit b₁, .lit b₂, _, _, hf => by
    simpa using hf (λ _ => false)



end BDD
