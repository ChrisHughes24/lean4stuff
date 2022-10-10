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

def bud : (z : Z P) → Type
| Z.bud => Unit
| Z.some a f => Σ (a : P.β a), bud (f a)

def extend : (z : Z P) → (b : bud z → P.α) → Z P
| Z.bud, b => Z.some (b ()) (λ _ => Z.bud)
| Z.some a f, b => Z.some a (λ bpa => extend (f bpa) (λ bf => b ⟨bpa, bf⟩))

theorem extend_injective_right : {z : Z P} → {b₁ b₂ : bud z → P.α} → 
  extend z b₁ = extend z b₂ → b₁ = b₂
| Z.bud, b₁, b₂, h => funext (λ x => by
cases x; simp [extend] at h; exact h.1)
| Z.some a f, b₁, b₂, h => by
  apply funext
  intro x
  simp [extend] at h
  dsimp [bud] at x
  match x with 
  | ⟨x₁, x₂⟩ => exact congrFun (extend_injective_right (congrFun h x₁)) x₂

@[simp] def bud_of_bud_extend : {z : Z P} → {bz : bud z → P.α} → (b : bud (extend z bz)) → bud z
| Z.bud, _, _ => ()
| Z.some _ _, _, ⟨pba, b⟩ => ⟨pba, bud_of_bud_extend b⟩

@[simp] def β_of_bud_extend : {z : Z P} → {bz : bud z → P.α} → (b : bud (extend z bz)) → 
  P.β (bz (bud_of_bud_extend b))
| Z.bud, _, b => b.1
| Z.some _ _, _, ⟨_, b⟩ => β_of_bud_extend b

def mk_bud_extend : (z : Z P) → (bz : bud z → P.α) → (b : bud z) → 
  (bp : P.β (bz b)) → bud (extend z bz) 
| Z.bud, _, _, bp => ⟨bp, ()⟩
| Z.some _ _, _, b, bp => ⟨b.1, mk_bud_extend _ _ b.2 bp⟩

@[simp] theorem bud_of_bud_extend_mk_bud_extend : {z : Z P} → {bz : bud z → P.α} 
  → (b : bud z) → (bp : P.β (bz b)) → bud_of_bud_extend (mk_bud_extend z bz b bp) = b
| Z.bud, _, _, _ => rfl
| Z.some a f, bz, ⟨_, _⟩, bp => by 
simp [bud_of_bud_extend, mk_bud_extend]
simp [bud_of_bud_extend_mk_bud_extend]

@[simp] theorem β_of_bud_extend_mk_bud_extend : {z : Z P} → {bz : bud z → P.α} 
  → (b : bud z) → (bp : P.β (bz b)) → β_of_bud_extend (mk_bud_extend z bz b bp) = 
    cast (by simp) bp 
| Z.bud, _, _, _ => rfl
| Z.some _ _, _, _, _ => by
simp [β_of_bud_extend, mk_bud_extend]
simp [β_of_bud_extend_mk_bud_extend]

structure M (P : PFunctor) : Type :=
( seq : Nat → Z P )
( leaf : (n : Nat) → bud (seq n) → P.α )
( zero_eq : seq 0 = Z.bud )
( succ_eq : (n : Nat) → seq (n+1) = extend (seq n) (leaf n) )

theorem M_ext : {m₁ m₂ : M P} → (h : ∀ n, m₁.seq n = m₂.seq n) → m₁ = m₂ 
| ⟨seq₁, leaf₁, zero_eq₁, succ_eq₁⟩, 
  ⟨seq₂, leaf₂, zero_eq₂, succ_eq₂⟩, h => by
simp only [M.mk.injEq]
have hseq : seq₁ = seq₂ := funext h
subst hseq
simp
apply funext
intro n
apply funext
intro b
have := (succ_eq₁ n).symm.trans (succ_eq₂ n)
rw [extend_injective_right this]

theorem M_ext2 {m₁ m₂ : M P} (h : ∀ (n : Nat) (h : m₁.seq n = m₂.seq n),
  m₁.leaf n = (λ b => m₂.leaf n (by rw [← h]; exact b))) : m₁ = m₂ := by
apply M_ext
intro n
induction n with
| zero => simp [M.zero_eq]
| succ n ih => sorry

def bud_zero {m : M P} : bud (m.seq 0) :=
cast (by rw [M.zero_eq]; rfl) ()

def bud_succ {m : M P} {n : Nat} (b : bud (m.seq n)) (bp : P.β (m.leaf n b)) : bud (m.seq (n+1)) :=
by rw [M.succ_eq]; exact mk_bud_extend _ (m.leaf n) b bp

--theorem bud_of_bud_extend_bud_succ

def bud_of_bud_succ {m : M P} {n : Nat} (b : bud (m.seq (n+1))) : bud (m.seq n) :=
by rw [M.succ_eq] at b; exact bud_of_bud_extend b

def M_coalg_seq_aux (m : M P) (p : P.β (m.leaf 0 bud_zero)) : 
  (n : Nat) → (z : Z P) × (bud z → bud (m.seq (n+1)))
| 0 => ⟨Z.bud, λ _ => bud_succ bud_zero p⟩
| n+1 => 
let sn := M_coalg_seq_aux m p n
⟨extend sn.1 (λ b =>  m.leaf _ (sn.2 b)), 
  λ b => bud_succ (sn.2 (bud_of_bud_extend b)) (β_of_bud_extend b) ⟩ 

def M_coalg (m : M P) : P.obj (M P) :=
⟨m.leaf 0 bud_zero, 
  λ b => 
    { seq := λ n => (M_coalg_seq_aux m b n).1,
      leaf := λ n b' => 
        M.leaf m n.succ (Sigma.snd (M_coalg_seq_aux m b n) b'),
      zero_eq := rfl,
      succ_eq := λ n => by rfl }⟩

theorem M_coalg_snd (m : M P) : (M_coalg m).2 = 
   λ b => 
    { seq := λ n => (M_coalg_seq_aux m b n).1,
      leaf := λ n => _,
      zero_eq := rfl,
      succ_eq := λ n => by rfl } := rfl

theorem M_coalg_snd_app_seq (m : M P) 
  (b : P.β (M_coalg m).1) : ((M_coalg m).2 b).seq = 
    λ n => (M_coalg_seq_aux m b n).1 := rfl

def to_M_seq_aux {A : Type} (coalg : A → P.obj A) (a : A) : 
  Nat → (z : Z P) × (bud z → A)
| 0 => ⟨Z.bud, λ _ => a⟩
| n+1 => let ⟨z, bz⟩ := to_M_seq_aux coalg a n
  ⟨extend z
    (λ b => (coalg (bz b)).1),
     λ b => bz (bud_of_bud_extend b) ⟩

def to_M {A : Type} (coalg : A → P.obj A) (a : A) : M P :=
{ seq := λ n => (to_M_seq_aux coalg a n).1,
  leaf := λ n b => (coalg ((to_M_seq_aux coalg a n).2 b)).1,
  zero_eq := rfl,
  succ_eq := λ _ => rfl }

theorem obj_ext {A : Type} {a b : P.obj A} 
  (h₁ : a.1 = b.1) (h₂ : ∀ (x : P.β a.1), a.2 x = b.2 (cast (by rw [h₁]) x)) :
  a = b := 
match a, b with
| ⟨a₁, a₂⟩, ⟨b₁, b₂⟩ => by
dsimp at h₁
subst h₁
dsimp [cast] at h₂
simp [funext h₂]

theorem coalg_to_M {A : Type} (coalg : A → P.obj A) (a : A) 
  (x : P.β (M_coalg (to_M coalg a)).1) (n : Nat) :
  M.leaf ((M_coalg (to_M coalg a)).2 x) n = sorry :=
by 
  dsimp [M_coalg, to_M, to_M_seq_aux,
    M_coalg_seq_aux]
  simp

-- theorem to_M_hom {A : Type} (coalg : A → P.obj A) (a : A) :
--   M_coalg (to_M coalg a) = P.map (to_M coalg) (coalg a) :=  
-- obj_ext rfl $ by
-- intro x
-- apply M_ext2
-- intro n h
-- simp
-- conv => 
--   congr 
--   delta to_M
--   delta M_coalg
--   dsimp



theorem to_M_unique_aux {A : Type} (coalg : A → P.obj A) (a : A) 
  (f : A → M P) (f_hom : ∀ (a : A), M_coalg (f a) = P.map f (coalg a)) :
  (n : Nat) → (show Σ (z : Z P), bud z → P.α from ⟨(f a).seq n, (f a).leaf n⟩) =
  ⟨(to_M_seq_aux coalg a n).1, 
    λ b => (coalg ((to_M_seq_aux coalg a n).2 b)).1⟩
| 0 => by
  specialize f_hom a
  have := congrArg Sigma.fst f_hom
  dsimp [M_coalg] at this ⊢
  apply Sigma.ext <;>
  simp [to_M_seq_aux, M.zero_eq]
  apply funext
  intro x
  refine Eq.trans sorry (Eq.trans this ?x)
  rw [PFunctor.map]
  dsimp
  sorry
| n+1 => by
  dsimp
  apply Sigma.ext <;>
  simp [to_M_seq_aux, M.succ_eq]
  have := to_M_unique_aux coalg a f f_hom n
  dsimp at this

  


theorem to_M_unique {A : Type} (coalg : A → P.obj A) (a : A) 
  (f : A → M P) (f_hom : ∀ (a : A), M_coalg (f a) = P.map f (coalg a)) (a : A) :
  f a = to_M coalg a := by
apply M_ext
intro n
induction n generalizing a with
| zero => simp [M.zero_eq]
| succ n ih => 
simp [M.succ_eq, to_M, to_M_seq_aux] at ih ⊢
simp [M_coalg, PFunctor.map] at f_hom
specialize ih a
dsimp at f_hom



-- . rw [M.zero_eq, M.zero_eq]
-- . rw [M.succ_eq, M.succ_eq]



end PFunctor