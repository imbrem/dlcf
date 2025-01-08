import DLCF.Syntax.Subst
import Mathlib.Data.ENat.Basic

namespace DLCF

namespace Term

open SuccOrder

section JEq

variable {Λ} [DecidableEq Λ] [Level Λ] [maxU : LevelBound Λ]

inductive JEq : Finset (FVar Λ) → Term Λ → Term Λ → Term Λ → Prop
  -- Congruence
  | top_emp : JEq ∅ (.univ 0) ⊤ ⊤
  | top_cons (hA : JEq Γ (.univ n) A A) : JEq (insert ⟨i, A⟩ Γ) (.univ 0) ⊤ ⊤
  | var (hΓ : JEq Γ (.univ n) A A) (hx : ⟨i, A⟩ ∈ Γ) : JEq Γ A (.free i A) (.free i A)
  | bot (hΓ : JEq Γ (.univ 0) ⊤ ⊤) : JEq Γ (.univ 0) ⊥ ⊥
  | tt (hΓ : JEq Γ (.univ 0) ⊤ ⊤) : JEq Γ ⊤ (.epsilon ⊤) (.epsilon ⊤)
  | univ (hΓ : JEq Γ (.univ 0) ⊤ ⊤) (hn : (succ n) ∈ LevelBound.valid)
    : JEq Γ (.univ (succ n)) (.univ n) (.univ n)
  | trunc (hΓ : JEq Γ (.univ n) A B) : JEq Γ (.univ 0) (.trunc A) (.trunc B)
  | dite (hφ : JEq Γ (.univ 0) φ φ') (ht : JEq Γ A t t') (hf : JEq Γ A f f')
    : JEq Γ A (.dite φ t f) (.dite φ' t' f')
  | pi (hA : JEq Γ (.univ n) A A') (L : Finset ℕ)
    (h : ∀i ∉ L, JEq (insert ⟨i, A⟩ Γ) (.univ m)
    (B.bsubst (Term.free i A).b0)
    (B'.bsubst (Term.free i A).b0))
    : JEq Γ (.univ (n ⊔ m ⊔ (succ 0))) (.pi A B) (.pi A' B')
  | abs (hA : JEq Γ (.univ n) A A') (L : Finset ℕ)
    (h : ∀i ∉ L, JEq (insert ⟨i, A⟩ Γ) (B.bsubst (Term.free i A).b0)
    (b.bsubst (Term.free i A).b0)
    (b'.bsubst (Term.free i A).b0))
    : JEq Γ (.pi A B) (.abs A b) (.abs A' b')
  | app (hf : JEq Γ (.pi A B) f f') (ha : JEq Γ A a a')
    : JEq Γ (B.bsubst a.b0) (.app f a) (.app f' a')
  -- Reduction rules
  | dite_top (ht : JEq Γ A t t') (hf : JEq Γ A f f') : JEq Γ A (.dite ⊤ t f) t'
  | dite_bot (ht : JEq Γ A t t') (hf : JEq Γ A f f') : JEq Γ A (.dite ⊥ t f) f'
  | β_abs {a A b B : Term Λ}
    (hA : JEq Γ (.univ n) A A')
    (L : Finset ℕ)
    (h : ∀i ∉ L, JEq (insert ⟨i, A⟩ Γ) (B.bsubst (Term.free i A).b0)
    (b.bsubst (Term.free i A).b0)
    (b.bsubst (Term.free i A).b0))
    (ha : JEq Γ A a a')
    : JEq Γ (B.bsubst a.b0) (.app (.abs A b) a) (b.bsubst a.b0)
  -- Axioms
  | pr_ext (hA : JEq Γ (.univ 0) A A') (hB : JEq Γ (.univ 0) B B')
    (hf : JEq Γ (.arr A B) f f') (hg : JEq Γ (.arr B A) g g')
    : JEq Γ (.univ 0) A B
  -- Casting
  | cast (h : JEq Γ (.univ n) A B) (hab : JEq Γ A a b) : JEq Γ B a b
  -- Partial equivalence
  | trans (hab : JEq Γ A a b) (hbc : JEq Γ B b c) : JEq Γ A a c
  | symm (hab : JEq Γ A a b) : JEq Γ A b a

attribute [simp] JEq.top_emp

notation Γ " ⊢ " a " ≡ " b " : " A => JEq Γ A a b

variable {Γ : Finset (FVar Λ)}

theorem JEq.to_top (h : Γ ⊢ a ≡ b : A) : Γ ⊢ ⊤ ≡ ⊤ : .univ 0
  := by induction h with
  | top_emp => exact .top_emp
  | top_cons hA => exact .top_cons hA
  | _ => assumption

theorem JEq.left_refl_jeq (h : Γ ⊢ a ≡ b : A) : Γ ⊢ a ≡ a : A := .trans h (.symm h)

theorem JEq.right_refl_jeq (h : Γ ⊢ a ≡ b : A) : Γ ⊢ b ≡ b : A := .trans (.symm h) h

def Ok (Γ : Finset (FVar Λ)) : Prop := ∃a b A, Γ ⊢ a ≡ b : A

theorem JEq.ok (h : Γ ⊢ a ≡ b : A) : Ok Γ := ⟨_, _, _, h⟩

theorem JEq.ok_var (h : Γ ⊢ A ≡ A' : .univ n) (i) : Ok (insert ⟨i, A⟩ Γ)
  := ⟨_, _, _, .top_cons h.left_refl_jeq⟩

theorem Ok.top (h : Ok Γ) : Γ ⊢ ⊤ ≡ ⊤ : .univ 0 := by have ⟨_, _, _, h⟩ := h; exact h.to_top

@[simp]
theorem JEq.top_iff : (Γ ⊢ ⊤ ≡ ⊤ : .univ 0) ↔ Ok Γ := ⟨JEq.ok, Ok.top⟩

theorem Ok.bot (h : Ok Γ) : Γ ⊢ ⊥ ≡ ⊥ : .univ 0 := .bot h.top

@[simp]
theorem JEq.bot_iff : (Γ ⊢ ⊥ ≡ ⊥ : .univ 0) ↔ Ok Γ := ⟨JEq.ok, Ok.bot⟩

theorem Ok.tt (h : Ok Γ) : Γ ⊢ .epsilon ⊤ ≡ .epsilon ⊤ : ⊤ := .tt h.top

@[simp]
theorem JEq.tt_iff : (Γ ⊢ .epsilon ⊤ ≡ .epsilon ⊤ : ⊤) ↔ Ok Γ := ⟨JEq.ok, Ok.tt⟩

theorem Ok.univ (h : Ok Γ) (hℓ : succ n ∈ LevelBound.valid) : Γ ⊢ .univ n ≡ .univ n : .univ (succ n)
  := .univ h.top hℓ

-- @[simp]
-- theorem JEq.univ_iff : (Γ ⊢ .univ n ≡ .univ n : .univ (succ n)) ↔ Ok Γ := ⟨JEq.ok, Ok.univ⟩

theorem JEq.wk (hΔ : Ok Δ) (w : Γ ⊆ Δ) (h : Γ ⊢ a ≡ b : A) : Δ ⊢ a ≡ b : A
  := by induction h generalizing Δ with
  | top_emp | top_cons => exact hΔ.top
  | trans hab hbc Iab Ibc => exact .trans (Iab hΔ w) (Ibc hΔ w)
  | symm hab I => exact .symm (I hΔ w)
  | _ => constructor
    <;> intros
    <;> (repeat first
    | assumption
    | apply JEq.ok_var
    | apply Finset.insert_subset_insert
    | apply_assumption)

theorem JEq.wki (h : Γ ⊢ a ≡ b : A) (hB : Γ ⊢ B ≡ B' : .univ n): insert ⟨i, B⟩ Γ ⊢ a ≡ b : A
  := h.wk (hB.ok_var i) (by simp)

theorem JEq.arr (hA : Γ ⊢ A ≡ A' : .univ n) (hB : Γ ⊢ B ≡ B' : .univ m)
  : Γ ⊢ .arr A B ≡ .arr A' B' : .univ (n ⊔ m ⊔ (succ 0)) := by
  apply JEq.pi hA ∅
  intro i
  simp only [Finset.not_mem_empty, not_false_eq_true, bsubst0_wk0, forall_const]
  apply hB.wki hA

theorem JEq.mem_exists (h : Γ ⊢ a ≡ b : A) (hx : ⟨i, B⟩ ∈ Γ)
  : ∃n, Γ ⊢ B ≡ B : .univ n := by induction h with
  | top_emp => cases hx
  | top_cons hA IA =>
    simp only [Finset.mem_insert, FVar.mk.injEq] at hx
    cases hx with
    | inl hx => cases hx.1; cases hx.2; exact ⟨_, hA.wki hA⟩
    | inr hx => have ⟨n, IA⟩ := IA hx; exact ⟨n, IA.wki hA⟩
  | _ => apply_assumption; assumption

theorem Ok.mem_exists (h : Ok Γ) (hA : ⟨i, A⟩ ∈ Γ) : ∃n, Γ ⊢ A ≡ A : .univ n := h.top.mem_exists hA

theorem Ok.var (h : Ok Γ) (hx : ⟨i, A⟩ ∈ Γ) : Γ ⊢ .free i A ≡ .free i A : A
  := have ⟨_, hA⟩ := h.mem_exists hx; .var hA hx

-- inductive OkL : List (FVar Λ) → Prop
--   | nil : OkL []
--   | cons (hA : Γ.toFinset ⊢ A ≡ A : .univ n) (hΓ : OkL Γ) : OkL (⟨i, A⟩ :: Γ)

end JEq

section CastU

variable {Λ} [DecidableEq Λ] [Level Λ]

theorem JEq.cast_maxU
  {lo hi : LevelBound Λ}
  (hb : lo ≤ hi)
  (h : JEq (maxU := lo) Γ A a b)
  : JEq (maxU := hi) Γ A a b := by induction h with
  | univ hΓ hℓ IΓ => exact .univ IΓ (hb hℓ)
  | cast => apply JEq.cast <;> assumption
  | trans => apply JEq.trans <;> assumption
  | symm => apply JEq.symm; assumption
  | _ => constructor <;> intros <;> apply_assumption <;> assumption

end CastU

section HasTy

variable {Λ} [DecidableEq Λ] [Level Λ] [maxU : LevelBound Λ]

inductive HasTy : Finset (FVar Λ) → Term Λ → Term Λ → Prop
  | var (hΓ : Ok Γ) (hx : ⟨i, A⟩ ∈ Γ) : HasTy Γ A (.free i A)
  | top (hΓ : Ok Γ) : HasTy Γ (.univ 0) ⊤
  | bot (hΓ : Ok Γ) : HasTy Γ (.univ 0) ⊥
  | tt (hΓ : Ok Γ) : HasTy Γ ⊤ (.epsilon ⊤)
  | univ (hΓ : Ok Γ) (hℓ : succ n ∈ LevelBound.valid) : HasTy Γ (.univ (succ n)) (.univ n)
  | dite (hφ : HasTy Γ (.univ 0) φ) (ht : HasTy Γ A t) (hf : HasTy Γ A f)
    : HasTy Γ A (.dite φ t f)
  | pi (hA : HasTy Γ (.univ n) A) (L : Finset ℕ)
    (hB : ∀i ∉ L, HasTy (insert ⟨i, A⟩ Γ) (.univ m) (B.bsubst (Term.free i A).b0))
    : HasTy Γ (.univ (n ⊔ m ⊔ (succ 0))) (.pi A B)
  | cast (h : Γ ⊢ A ≡ B : .univ n) (ha : HasTy Γ A a) : HasTy Γ B a

notation Γ " ⊢ " a " : " A => HasTy Γ A a

variable {Γ : Finset (FVar Λ)}

theorem HasTy.ok (h : Γ ⊢ a : A) : Ok Γ := by induction h with
  | _ => assumption

theorem HasTy.refl (h : Γ ⊢ a : A) : Γ ⊢ a ≡ a : A := by induction h with
  | top hΓ => exact hΓ.top
  | var hΓ hx => exact hΓ.var hx
  | cast h ha Ia => exact .cast h Ia
  | _ => constructor <;> (try apply Ok.top) <;> assumption

theorem HasTy.ok_var (h : Γ ⊢ A : .univ n) (i) : Ok (insert ⟨i, A⟩ Γ) := h.refl.ok_var i

theorem HasTy.wk (hΔ : Ok Δ) (w : Γ ⊆ Δ) (h : Γ ⊢ a : A) : Δ ⊢ a : A
  := by induction h generalizing Δ with
  | var _ hx => exact .var hΔ (w hx)
  | cast h ha Ia => exact (Ia hΔ w).cast (h.wk hΔ w)
  | _ => constructor
    <;> intros
    <;> (repeat first
    | assumption
    | apply HasTy.ok_var
    | apply Finset.insert_subset_insert
    | apply_assumption)

end HasTy

-- inductive Ext : Finset FVar → Finset FVar → Prop
--   | emp (hΓ : Ok Γ) : Ext Γ ∅
--   | cons (hΓ : Ext Γ Δ) (hA : (Γ ∪ Δ) ⊢ A ≡ A : .univ n) : Ext Γ (insert ⟨i, A⟩ Δ)

-- theorem Ext.left (hΓ : Ext Γ Δ) : Ok Γ := by induction hΓ <;> assumption

-- theorem Ext.ok (h : Ext Γ Δ) : Ok (Γ ∪ Δ) := by induction h with
--   | emp hΓ => rw [Finset.union_empty]; exact hΓ
--   | cons hΓ hA => rw [Finset.union_insert]; exact hA.ok_var _

-- theorem Ext.right (h : Ext ∅ Δ) : Ok Δ := by convert h.ok; rw [Finset.empty_union]

-- theorem JEq.ext_singleton (i) (h : Γ ⊢ A ≡ A : .univ n) : Ext Γ {⟨i, A⟩}
--   := .cons (.emp h.ok) (by convert h; simp)

-- theorem Ext.jeq (hΔ : Ext Γ Δ) (h : Γ ⊢ a ≡ b : A) : (Γ ∪ Δ) ⊢ a ≡ b : A
--   := by induction h generalizing Δ with
--   | top_emp => simp [hΔ.right]
--   | top_cons hA I => convert hΔ.ok; simp
--   | var hΓ hx IΓ => exact .var (IΓ hΔ) (by simp [hx])
--   | trans hab hbc Iab Ibc => exact .trans (Iab hΔ) (Ibc hΔ)
--   | symm hab I => exact .symm (I hΔ)
--   | pi hA L hB IA IB =>
--     simp only [Finset.insert_union] at *
--     constructor
--     apply_assumption; assumption
--     intros i hi
--     apply IB
--     assumption
--     sorry
--   | _ => constructor <;> apply_assumption; assumption
