structure PFunctor : Type 1 :=
( α : Type )
( β : α → Type )

variable (P : PFunctor)

namespace PFunctor

def obj (X : Type) : Type :=
Σ (a : P.α), P.β a → X

def map {X Y : Type} (f : X → Y) (x : P.obj X) : P.obj Y :=
⟨x.1, λ a => f (x.2 a)⟩

inductive Z (P : PFunctor) : Type
| bud : Z P
| some (a : P.α) (f : P.β a → Z P) : Z P

variable {P}

def of_α (a : P.α) : Z P :=
Z.some a (λ _ => Z.bud)

inductive bud : Z P → Type
| bud : bud (@Z.bud P)
| some {a : P.α} {f : P.β a → Z P} {p : P.β a} (b : bud (f p)) : 
    bud (Z.some a f)

inductive is_extension : Z P → Z P → Prop
| bud (z : Z P) : is_extension Z.bud z
| some {a : P.α} {f₁ f₂ : P.β a → Z P} (h : ∀ p : P.β a, is_extension (f₁ p) (f₂ p)) :
  is_extension (Z.some a f₁) (Z.some a f₂)

theorem is_extension.refl : (z : Z P) → is_extension z z
| Z.bud => is_extension.bud _
| Z.some _ _ => is_extension.some (λ _ => is_extension.refl _)

inductive extends_at {P : PFunctor}: (z₁ : Z P) → (b : bud z) → Z P → Type
| bud {a : P.α} {f : P.β a → Z P} : extends_at (@Z.bud P) (@bud.bud P) (Z.some a f)
| some {a : P.α} {f₁ f₂ : P.β a → Z P} {p : P.β a} (b : bud (f₁ p)) 
  (h : extends_at (f₁ p) b (f₂ p)) :  
    extends_at (Z.some a f₁) (bud.some b) (Z.some a f₂)

structure M' (P : PFunctor) : Type :=
( s : Z P → Prop )
( bud_mem : s Z.bud )
( extension_pair {z₁ z₂ : Z P} : s z₁ → s z₂ → 
  ∃ z₃ : Z P, s z₃ ∧ is_extension z₁ z₃ ∧ is_extension z₂ z₃ )
( extend {z : Z P} : s z → bud z → Z P )
( extend_extends {z : Z P} (h : s z) (b : bud z) : 
    extends_at z b (extend h b) )

def M'.constructor (m : M' P) : P.α :=
let z := m.extend m.bud_mem bud.bud
have hz : extends_at Z.bud bud.bud z := m.extend_extends m.bud_mem bud.bud
match z, hz with
| Z.some a _, _ => a

def M.branch (m : M' P) (a : P.β m.constructor) : M' P :=

def M'_coalg (m : M' P) : P.obj (M' P) :=
let z := m.extend m.bud_mem bud.bud
have hz : extends_at Z.bud bud.bud z := m.extend_extends m.bud_mem bud.bud
match z, hz with
| Z.some a f, _ => ⟨a, λ p => 
  { s := λ z => z = Z.bud ∨ ∃ f : P.β a → Z P, m.s (Z.some a f) ∧ z = f p,
    bud_mem := Or.inl rfl,
    extension_pair := @λ z₁ z₂ hz₁ hz₂ => 
      match z₁, z₂, hz₁, hz₂ with 
      | _, z₂, Or.inl rfl, hz₂ => 
        ⟨z₂, hz₂, is_extension.bud _, is_extension.refl _⟩
      | z₁, _, hz₁, Or.inl rfl => 
        ⟨z₁, hz₁, is_extension.refl _, is_extension.bud _⟩
      | _, _, Or.inr ⟨f₁, hf₁, rfl⟩, Or.inr ⟨f₂, hf₂, rfl⟩ => 
        match m.extension_pair hf₁ hf₂ with
        | ⟨Z.some _ f, h₁, is_extension.some h₂, is_extension.some h₃⟩ => 
          ⟨f p, Or.inr ⟨f, h₁, rfl⟩, h₂ p, h₃ p⟩,
    extend := @λ z hz b => 
      match z, hz, b with
      | Z.bud, _, bud.bud => f p
      | Z.some a' f', h, @bud.some _ _ _ p' h' => 
        _
    extend_extends := sorry
       }⟩

-- def M'.rel (m₁ m₂ : M' P) : Prop :=
-- ∃ m₃ : M' P, (∀ z, m₁.s z → m₃.s z) ∧ (∀ z, m₂.s z → m₃.s z)

-- def M'.rel.refl (m : M' P) : M'.rel m m :=
-- ⟨m, λ _ => id, λ _ => id⟩

-- def M'.rel.symm {m₁ m₂ : M' P} : M'.rel m₁ m₂ → M'.rel m₂ m₁ 
-- | ⟨m₃, h₁, h₂⟩ => ⟨m₃, h₂, h₁⟩

-- def M'.rel.trans {m₁ m₂ m₃ : M' P} : M'.rel m₁ m₂ → M'.rel m₂ m₃ → M'.rel m₁ m₃
-- | ⟨n, hn₁, hn₂⟩, ⟨o, ho₁, ho₂⟩ => 
--   ⟨{ s := λ z => n.s z ∨ o.s z,
--      bud_mem := Or.inl n.s.bud_mem,
--      extension_pair := _  }  
