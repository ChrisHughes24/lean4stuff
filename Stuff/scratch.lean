inductive unit (p : Prop) : Type
| intro : unit p
deriving DecidableEq

section

variable {A B C  : Type}

def ProdFun (f : A → B) (g : A → C) : A → (B × C) := λ a => (f a, g a)

example (f : C → A × B) (a : C) : f a = ((f a).1, (f a).2) := rfl

theorem ProdFunFst (f : A → B) (g : A → C) : Prod.fst ∘ ProdFun f g = f := rfl

theorem ProdFunSnd (f : A → B) (g : A → C) : Prod.snd ∘ ProdFun f g = g := rfl

theorem ProdFunEta (f : A → B × C) :
  f = ProdFun (Prod.fst ∘ f) (Prod.snd ∘ f) := rfl


theorem sumEta (Y : (A ⊕ B) → Type) (f : (a : A ⊕ B) → Y a) :
  f = λ a => match a with
  | Sum.inl a => f (Sum.inl a)
  | Sum.inr b => f (Sum.inr b) :=
  by
    funext a
    cases a
    rfl
    rfl

end



variable {A : Type} {B : A → Type} {C : Type}

def SigmaFun (f : (a : A) → B a → C) : (Σ a, B a) → C :=
λ a => f a.1 a.2

def SigmaFunIn (f : (a : A) → B a → C) (a : A) (b : B a) : SigmaFun f ⟨a, b⟩ = f a b := rfl

theorem SigmaFunEta (f : (Σ a, B a) → C) :
  f = SigmaFun (λ a b => f ⟨a, b⟩) := rfl

def PiFun (f : (a : A) → C → B a) : C → (a : A) → B a := λ c a => f a c

def PiFunIn (f : (a : A) → C → B a) (c : C) (a : A) : PiFun f c a = f a c := rfl

theorem PiFunEta (f : C → (a : A) → B a) :
  f = PiFun (λ a c => f c a) := rfl
