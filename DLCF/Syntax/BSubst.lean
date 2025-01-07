import DLCF.Syntax.Basic

namespace DLCF

namespace Term

variable {Λ}

def BSubst (Λ) := ℕ → Term Λ

def b0 (t : Term Λ) : BSubst Λ
  | 0 => t
  | n + 1 => .bound n

def BSubst.lift (σ : BSubst Λ) : BSubst Λ
  | 0 => bound 0
  | n + 1 => (σ n).wk0

def bsubst (σ : BSubst Λ) : Term Λ → Term Λ
  | bound n => σ n
  | univ n => univ n
  | epsilon A => epsilon (A.bsubst σ)
  | dite c t f => dite (c.bsubst σ) (t.bsubst σ.lift) (f.bsubst σ.lift)
  | pi A B => pi (A.bsubst σ) (B.bsubst (σ.lift))
  | app f a => app (f.bsubst σ) (a.bsubst σ)
  | abs A t => abs (A.bsubst σ) (t.bsubst (σ.lift))
  | eq A a b => eq (A.bsubst σ) (a.bsubst σ) (b.bsubst σ)
  | sigma f => sigma (f.bsubst σ)
  | mks f => mks (f.bsubst σ)
  | srec f => srec (f.bsubst σ)
  | wty f => wty (f.bsubst σ)
  | mkw f => mkw (f.bsubst σ)
  | wrec f => wrec (f.bsubst σ)
  | qty f => qty (f.bsubst σ)
  | mkq f => mkq (f.bsubst σ)
  | qrec f => qrec (f.bsubst σ)
  | t => t

def BSubst.id : BSubst Λ := .bound

@[simp]
theorem BSubst.lift_id : BSubst.id.lift = BSubst.id (Λ := Λ)
  := funext (λn => by cases n <;> simp [id, lift, wk0, wk])

@[simp]
theorem BSubst.id_applied (n : ℕ) : BSubst.id (Λ := Λ) n = bound n := rfl

@[simp]
theorem bsubst_id (t : Term Λ) : t.bsubst BSubst.id = t := by induction t <;> simp [bsubst, *]

def BSubst.comp (σ τ : BSubst Λ) : BSubst Λ := λn => (τ n).bsubst σ

@[simp]
theorem BSubst.comp_id (σ : BSubst Λ) : σ.comp id = σ :=  rfl

@[simp]
theorem BSubst.id_comp (σ : BSubst Λ) : id.comp σ = σ := funext (λn => by simp [comp])

def BSubst.ofWk (ρ : ℕ → ℕ) : BSubst Λ := bound ∘ ρ

@[simp]
theorem BSubst.ofWk_applied (ρ : ℕ → ℕ) (n : ℕ) : (BSubst.ofWk (Λ := Λ) ρ) n = bound (ρ n) := rfl

theorem BSubst.ofWk_id : ofWk _root_.id = id (Λ := Λ) := rfl

theorem BSubst.ofWk_comp (ρ ρ' : ℕ → ℕ) : ofWk (Λ := Λ) (ρ ∘ ρ') = (ofWk ρ).comp (ofWk ρ') := rfl

@[simp]
theorem b0_comp_wk0 (t : Term Λ) : t.b0.comp (BSubst.ofWk .succ) = BSubst.id
  := by funext k; cases k <;> rfl

abbrev BSubst.wkIn (ρ : ℕ → ℕ) (σ : BSubst Λ) : BSubst Λ := σ ∘ ρ

abbrev BSubst.wkOut (ρ : ℕ → ℕ) (σ : BSubst Λ) : BSubst Λ := (λn => (σ n).wk ρ)

theorem BSubst.lift_wkIn (σ : BSubst Λ) (ρ : ℕ → ℕ)
  : (σ.wkIn ρ).lift = σ.lift.wkIn (Nat.liftWk ρ) := funext (λn => by cases n <;> rfl)

theorem bsubst_wkIn (σ : BSubst Λ) (ρ : ℕ → ℕ) (t : Term Λ)
  : t.bsubst (σ.wkIn ρ) = (t.wk ρ).bsubst σ
  := by induction t generalizing σ ρ <;> simp [bsubst, BSubst.lift_wkIn, *]

theorem BSubst.lift_wkOut (σ : BSubst Λ) (ρ : ℕ → ℕ)
  : (σ.wkOut ρ).lift = σ.lift.wkOut (Nat.liftWk ρ) := funext (λn =>
  by cases n <;> simp [wkOut, Nat.liftWk, lift, wk, wk0, <-wk_comp, Nat.liftWk_comp_succ])

theorem bsubst_wkOut (σ : BSubst Λ) (ρ : ℕ → ℕ) (t : Term Λ)
  : t.bsubst (σ.wkOut ρ) = (t.bsubst σ).wk ρ
  := by induction t generalizing σ ρ <;> simp [bsubst, wk, BSubst.lift_wkOut, *]

abbrev BSubst.wkIn0 := wkIn (Λ := Λ) .succ

abbrev BSubst.wkOut0 := wkOut (Λ := Λ) .succ

theorem bsubst_wkIn0 (σ : BSubst Λ) (t : Term Λ) : t.bsubst (σ.wkIn0) = (t.wk0).bsubst σ
  := bsubst_wkIn σ .succ t

theorem bsubst_wkOut0 (σ : BSubst Λ) (t : Term Λ) : t.bsubst (σ.wkOut0) = (t.bsubst σ).wk0
  := bsubst_wkOut σ .succ t

theorem BSubst.wkIn0_lift (σ : BSubst Λ) : σ.lift.wkIn0 = σ.wkOut0
  := funext (λn => by cases n <;> rfl)

theorem BSubst.lift_comp (σ τ : BSubst Λ) : (σ.comp τ).lift = σ.lift.comp τ.lift := funext (λn
  => by cases n <;> simp [bsubst, comp, lift, <-bsubst_wkIn0, <-bsubst_wkOut0, BSubst.wkIn0_lift])

theorem bsubst_comp (σ τ : BSubst Λ) (t : Term Λ) : t.bsubst (σ.comp τ) = (t.bsubst τ).bsubst σ
  := by induction t generalizing σ τ <;> simp [bsubst, BSubst.comp, BSubst.lift_comp, *]

theorem BSubst.comp_assoc (σ τ ρ : BSubst Λ) : (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := funext (λn
  => by simp [BSubst.comp, bsubst_comp, *])

instance BSubst.instMonoid : Monoid (BSubst Λ) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem BSubst.lift_one : (1 : BSubst Λ).lift = 1 := BSubst.lift_id

@[simp]
theorem BSubst.one_applied (n : ℕ) : (1 : BSubst Λ) n = bound n := rfl

@[simp]
theorem bsubst_one (t : Term Λ) : t.bsubst 1 = t := bsubst_id t

theorem BSubst.lift_mul (σ τ : BSubst Λ) : (σ * τ).lift = σ.lift * τ.lift := BSubst.lift_comp σ τ

theorem bsubst_mul (σ τ : BSubst Λ) (t : Term Λ) : t.bsubst (σ * τ) = (t.bsubst τ).bsubst σ
  := bsubst_comp σ τ t

instance mulActionBSubst : MulAction (BSubst Λ) (Term Λ) where
  smul := bsubst
  one_smul := bsubst_one
  mul_smul := bsubst_mul

theorem BSubst.lift_ofWk (ρ : ℕ → ℕ) : (BSubst.ofWk ρ).lift (Λ := Λ) = BSubst.ofWk (Nat.liftWk ρ)
  := by funext n; cases n <;> rfl

theorem bsubst_ofWk (ρ : ℕ → ℕ) (t : Term Λ) : t.bsubst (BSubst.ofWk ρ) = t.wk ρ
  := by induction t generalizing ρ <;> simp [wk, bsubst, BSubst.lift_ofWk, *]

@[simp]
theorem bsubst0_wk0 (t s : Term Λ) : t.wk0.bsubst s.b0 = t
  := by simp [wk0, <-bsubst_ofWk, <-bsubst_comp]

theorem ofWk_smul (ρ : ℕ → ℕ) (t : Term Λ) : (BSubst.ofWk (Λ := Λ) ρ) • t = ρ • t := bsubst_ofWk ρ t

-- TODO: class-ify?
-- theorem bv_wk_le (ρ : ℕ → ℕ) (t : Term) (k : ℕ) (h : BoundedOn t.bv k ρ)
--   : (t.wk ρ).bv ≤ k := by
--   induction t generalizing ρ k with
--   | bound => apply h.bounded_on; simp [bv]
--   | _ =>
--     simp [bv, wk] <;>
--     (try constructorm* _ ∧ _) <;>
--     apply_assumption <;>
--     sorry

-- TODO: class-ify?
def BSubst.BoundedOn (src trg : ℕ) (σ : BSubst Λ) : Prop := ∀i ≤ src, (σ i).bv ≤ trg

-- theorem bv_bsubst_le (σ : BSubst) (t : Term) (k : ℕ) (h : ∀i < t.bv, (σ i).bv ≤ k)
--   : (t.bsubst σ).bv ≤ k := by
--   induction t generalizing σ k with
--   | bound => sorry
--   | _ =>
--     simp [bsubst, bv] <;>
--     (try constructorm* _ ∧ _) <;>
--     apply_assumption <;>
--     intros i hi <;>
--     (try apply_assumption) <;>
--     cases i <;>
--     simp [BSubst.lift, bv, *]
