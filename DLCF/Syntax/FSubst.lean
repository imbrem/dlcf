import DLCF.Syntax.Basic

namespace DLCF

namespace Term

def FSubst := FVar → Term

def FSubst.wk (ρ : ℕ → ℕ) (σ : FSubst) : FSubst := λx => (σ x).wk ρ

@[simp]
theorem FSubst.wk_applied (ρ : ℕ → ℕ) (σ : FSubst)
  : (σ.wk ρ) x = (σ x).wk ρ := rfl

@[simp]
theorem FSubst.wk_id (σ : FSubst) : σ.wk id = σ := by funext x; simp

theorem FSubst.wk_comp (ρ ρ' : ℕ → ℕ) (σ : FSubst)
  : σ.wk (ρ ∘ ρ') = (σ.wk ρ').wk ρ := by funext x; simp [Term.wk_comp]

instance FSubst.wkSMul : SMul (ℕ → ℕ) FSubst where
  smul := FSubst.wk

theorem FSubst.smul_wk_def (ρ : ℕ → ℕ) (σ : FSubst) : ρ • σ = σ.wk ρ := rfl

@[simp]
theorem FSubst.smul_wk_applied (ρ : ℕ → ℕ) (σ : FSubst) (x)
  : (ρ • σ) x = ρ • σ x := rfl

@[simp]
theorem FSubst.id_smul_wk (σ : FSubst) : _root_.id (α := ℕ) • σ = σ :=  wk_id σ

theorem FSubst.comp_smul_wk (ρ ρ' : ℕ → ℕ) (σ : FSubst)
  : (ρ ∘ ρ') • σ = ρ • (ρ' • σ) := wk_comp ρ ρ' σ

def FSubst.lift (σ : FSubst) : FSubst := σ.wk .succ

@[simp]
theorem FSubst.lift_applied (σ : FSubst) (x)
  : σ.lift x = (σ x).wk0 := rfl

def fsubst (σ : FSubst) : Term → Term
  | free n A => σ ⟨n, A⟩
  | pi A B => pi (A.fsubst σ) (B.fsubst σ.lift)
  | app f a => app (f.fsubst σ) (a.fsubst σ)
  | abs A t => abs (A.fsubst σ) (t.fsubst σ.lift)
  | eq A a b => eq (A.fsubst σ) (a.fsubst σ) (b.fsubst σ)
  | t => t

def FSubst.id : FSubst := λx => .free x.name x.ty

@[simp]
theorem FSubst.lift_id : id.lift = id := rfl

@[simp]
theorem FSubst.id_applied (x) : id x = x := rfl

@[simp]
theorem fsubst_id (t : Term) : t.fsubst FSubst.id = t := by
  induction t <;> simp [fsubst, *]

theorem wk_fsubst  (ρ : ℕ → ℕ) (σ : FSubst) (t : Term)
  : (t.fsubst σ).wk ρ = (t.wk ρ).fsubst (σ.wk ρ) := by
  induction t generalizing ρ σ
  <;> simp [wk, fsubst, FSubst.lift, <-FSubst.wk_comp, Nat.liftWk_comp_succ, *]

def FSubst.comp (σ τ : FSubst) : FSubst := λx => (τ x).fsubst σ

@[simp]
theorem FSubst.comp_applied (σ τ : FSubst) (x)
  : (σ.comp τ) x = (τ x).fsubst σ := rfl

@[simp] theorem FSubst.comp_id (σ : FSubst) : σ.comp id = σ := rfl

@[simp] theorem FSubst.id_comp (σ : FSubst) : id.comp σ = σ := by funext x; simp [comp]

theorem FSubst.comp_wk (ρ : ℕ → ℕ) (σ τ : FSubst)
  : (σ.comp τ).wk ρ = (σ.wk ρ).comp (τ.wk ρ) := by funext x; simp [comp, wk_fsubst, *]

theorem FSubst.lift_comp (σ τ : FSubst) : (σ.comp τ).lift = σ.lift.comp τ.lift := comp_wk .succ σ τ

theorem fsubst_comp (σ τ : FSubst) (t : Term) : t.fsubst (σ.comp τ) = (t.fsubst τ).fsubst σ
  := by induction t generalizing σ τ <;> simp [fsubst, FSubst.lift_comp, *]

theorem FSubst.comp_assoc (σ τ ρ : FSubst) : (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  funext x; simp [FSubst.comp, fsubst_comp, *]

instance FSubst.instMonoid : Monoid FSubst where
  one := id
  mul := comp
  one_mul := FSubst.id_comp
  mul_one := FSubst.comp_id
  mul_assoc := FSubst.comp_assoc

@[simp]
theorem FSubst.one_applied (x) : (1 : FSubst) x = x := rfl

theorem fsubst_one (t : Term) : t.fsubst 1 = t := fsubst_id t

theorem fsubst_mul (σ τ : FSubst) (t : Term)
  : t.fsubst (σ * τ) = (t.fsubst τ).fsubst σ := fsubst_comp σ τ t

instance mulActionFSubst : MulAction FSubst Term where
  smul := fsubst
  one_smul := fsubst_one
  mul_smul := fsubst_mul

theorem FSubst.lift_one : (1 : FSubst).lift = 1 := FSubst.lift_id

theorem FSubst.lift_mul (σ τ : FSubst) : (σ * τ).lift = σ.lift * τ.lift := FSubst.lift_comp σ τ

def FSubst.set (σ : FSubst) (x : FVar) (a : Term) : FSubst
  := Function.update σ x a

@[simp]
theorem FSubst.set_same (σ : FSubst) (x) (a : Term)
  : (σ.set x a) x = a := by simp [set]

@[simp]
theorem FSubst.set_idem (σ : FSubst) (a b : Term)
  : (σ.set x a).set x b = σ.set x b := by simp [set]

theorem FSubst.wk_set (ρ : ℕ → ℕ) (σ : FSubst) (x) (a : Term)
  : (σ.set x a).wk ρ = (σ.wk ρ).set x (a.wk ρ) := by
  funext y; simp only [set, wk_applied, Function.update, eq_rec_constant, dite_eq_ite]
  split <;> rfl

theorem FSubst.smul_wk_set (ρ : ℕ → ℕ) (σ : FSubst) (x) (a : Term)
  : ρ • (σ.set x a) = (ρ • σ).set x (a.wk ρ)
  := wk_set ρ σ x a

theorem FSubst.lift_set (σ : FSubst) (x) (a : Term)
  : (σ.set x a).lift = σ.lift.set x a.wk0 := wk_set .succ σ x a

def fset (t : Term) (x : FVar) (a : Term) : Term := t.fsubst (FSubst.id.set x a)

theorem FSubst.free_on_lift_iff {σ : FSubst} {V : Finset FVar}
  : (∀x ∈ V, σ.lift x = x) ↔ (∀x ∈ V, σ x = x)
  := by
  rw [forall_congr]
  intro x
  rw [imp_congr Iff.rfl]
  simp only [lift_applied, Term.wk0]
  generalize σ x = s
  cases s <;> simp [Term.wk]

theorem FSubst.free_on_lift {σ : FSubst} {V : Finset FVar} (h : ∀x ∈ V, σ x = x)
  : ∀x ∈ V, σ.lift x = x := free_on_lift_iff.mpr h

theorem fsubst_id_on (σ : FSubst) (t : Term) (h : ∀x ∈ t.fv, σ x = x)
  : t.fsubst σ = t := by induction t generalizing σ with
  | free n A => exact h ⟨n, A⟩ (by simp [fv])
  | _ =>
    simp [fsubst] <;>
    (try constructorm* _ ∧ _) <;>
    apply_assumption <;>
    intro x hx <;>
    (first | apply h | apply FSubst.free_on_lift h) <;>
    simp [fv, *]
