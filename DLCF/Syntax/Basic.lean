import Discretion.Wk.Nat
import Discretion.Wk.Finset

import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.UpperLower.Basic

import Mathlib.Data.Nat.SuccPred

namespace DLCF

class Level (Λ : Type _) extends SemilatticeSup Λ, SuccOrder Λ, Zero Λ, One Λ where
  one_eq_succ_zero : 1 = SuccOrder.succ (α := Λ) 0

class LevelBound (Λ : Type _) [Level Λ] where
  valid : Set Λ
  valid_lower: IsLowerSet valid
  one_valid : 1 ∈ valid

theorem LevelBound.zero_valid [Level Λ] [LevelBound Λ] : (0 : Λ) ∈ LevelBound.valid := by
  apply LevelBound.valid_lower _ LevelBound.one_valid
  rw [Level.one_eq_succ_zero]
  apply SuccOrder.le_succ

instance Level.instNat : Level ℕ where
  one_eq_succ_zero := rfl

instance LevelBound.instPartialOrder {Λ} [Level Λ] : PartialOrder (LevelBound Λ) where
  le a b := a.valid ⊆ b.valid
  le_refl a := le_refl a.valid
  le_trans a b c hab hbc := le_trans (α := Set Λ) hab hbc
  le_antisymm a b hab hba := by cases a; cases b; cases le_antisymm (α := Set Λ) hab hba; rfl

def LevelBound.no_universes (Λ : Type _) [Level Λ] : LevelBound Λ where
    valid := Set.Iic 1
    valid_lower := isLowerSet_Iic 1
    one_valid := le_refl 1

-- NOTE: this may diverge from `no_universes` if we add config flags for the type theory to
-- `LevelBound`.
instance LevelBound.instOrderBot (Λ : Type _) [Level Λ] : OrderBot (LevelBound Λ) where
  bot := no_universes Λ
  bot_le a _ hℓ := a.valid_lower hℓ a.one_valid

instance LevelBound.instOrderTop (Λ : Type _) [Level Λ] : OrderTop (LevelBound Λ) where
  top := {
    valid := Set.univ
    valid_lower := isLowerSet_univ
    one_valid := Set.mem_univ 1
  }
  le_top _ ℓ _ := Set.mem_univ ℓ

-- TODO: level bounds actually form a complete lattice

instance LevelBound.nat_unbounded : LevelBound ℕ := ⊤

variable (Λ : Type _)

inductive Term : Type
  | bound : ℕ → Term
  | free : ℕ → Term → Term
  | top : Term
  | bot : Term
  | trunc : Term → Term
  | epsilon : Term → Term
  | univ : Λ → Term
  | dite : Term → Term → Term → Term
  | pi : Term → Term → Term
  | app : Term → Term → Term
  | abs : Term → Term → Term
  | eq : Term → Term → Term → Term
  | sigma : Term → Term
  | mks : Term → Term
  | srec : Term → Term
  | wty : Term → Term
  | mkw : Term → Term
  | wrec : Term → Term
  | qty : Term → Term
  | mkq : Term → Term
  | qrec : Term → Term
  | invalid : Term
  deriving DecidableEq

structure Term.FVar where
  name : ℕ
  ty : Term Λ
  deriving DecidableEq

-- TODO: separate out primitives ε, Σ, W, Q, Σrec, Wrec, Qrec, mkΣ, mkW, mkQ?

instance : Inhabited (Term Λ) := ⟨.invalid⟩

instance : Top (Term Λ) := ⟨.top⟩

instance : Bot (Term Λ) := ⟨.bot⟩

namespace Term

variable {Λ : Type _}

inductive Sexpr : Type
  | of : String → Sexpr
  | cat : List Sexpr → Sexpr

def Sexpr.print_inner (opened : Bool) : Sexpr → String
  | .of s => s
  | .cat [] => if opened then ")" else "()"
  | .cat (x::xs) =>
    if opened then "(" else ""
      ++ (x.print_inner false)
      ++ " "
      ++ (Sexpr.cat xs).print_inner true

def Sexpr.print : Sexpr → String := print_inner false

instance : ToString Sexpr where toString := Sexpr.print

def sexpr [ToString Λ] : Term Λ → Sexpr
  | bound n => .of ("#" ++ toString n)
  | free n A => .cat [.of "#f", .of (toString n), A.sexpr]
  | top => .of "#⊤"
  | bot => .of "#⊥"
  | trunc A => .cat [.of "#T", A.sexpr]
  | univ ℓ => .cat [.of "#U", .of (toString ℓ)]
  | dite c t f => .cat [.of "#dite", c.sexpr, t.sexpr, f.sexpr]
  | epsilon A => .cat [.of "#ε", A.sexpr]
  | pi A B => .cat [.of "#Π", A.sexpr, B.sexpr]
  | app f a => .cat [.of "#.", f.sexpr, a.sexpr]
  | abs A t => .cat [.of "#λ", A.sexpr, t.sexpr]
  | eq A a b => .cat [.of "#=", A.sexpr, a.sexpr, b.sexpr]
  | sigma A => .cat [.of "#Σ", A.sexpr]
  | mks A => .cat [.of "#mkΣ", A.sexpr]
  | srec A => .cat [.of "#Σrec", A.sexpr]
  | wty A => .cat [.of "#W", A.sexpr]
  | mkw A => .cat [.of "#mkW", A.sexpr]
  | wrec A => .cat [.of "#Wrec", A.sexpr]
  | qty A => .cat [.of "#Q", A.sexpr]
  | mkq A => .cat [.of "#mkQ", A.sexpr]
  | qrec A => .cat [.of "#Qrec", A.sexpr]
  | invalid => .of "#X"

instance [ToString Λ] : ToString (Term Λ) where toString t := toString t.sexpr

def depth : Term Λ → ℕ
  | free _ A => A.depth + 1
  | epsilon A => A.depth + 1
  | dite c t f => (c.depth ⊔ t.depth ⊔ f.depth) + 1
  | pi A B => (A.depth ⊔ B.depth) + 1
  | app f a => (f.depth ⊔ a.depth) + 1
  | abs A t => (A.depth ⊔ t.depth) + 1
  | eq A a b => (A.depth ⊔ a.depth ⊔ b.depth) + 1
  | sigma f | mks f | srec f | wty f | mkw f | wrec f | qty f | mkq f | qrec f => f.depth + 1
  | _ => 0

def size : Term Λ → ℕ
  | free _ A => A.size + 1
  | epsilon A => A.size + 1
  | dite c t f => (c.size + t.size + f.size) + 1
  | pi A B => (A.size + B.size) + 1
  | app f a => (f.size + a.size) + 1
  | abs A t => (A.size + t.size) + 1
  | eq A a b => (A.size + a.size + b.size) + 1
  | sigma f | mks f | srec f | wty f | mkw f | wrec f | qty f | mkq f | qrec f => f.size + 1
  | _ => 1

theorem depth_lt_size (t : Term Λ) : t.depth < t.size := by
  induction t <;> simp [depth, size, *] <;> omega

-- theorem size_le_2_pow_depth (t : Term) : t.size ≤ 2 ^ t.depth := by
--   induction t <;> simp [depth, size, pow_succ, mul_two, *] <;> aesop

def bv : Term Λ → ℕ
  | bound n => n + 1
  | trunc A => A.bv
  | epsilon A => A.bv
  | dite c t f => c.bv ⊔ (t.bv - 1) ⊔ (f.bv - 1)
  | pi A B => A.bv ⊔ (B.bv - 1)
  | app f a => f.bv ⊔ a.bv
  | abs A t => A.bv ⊔ (t.bv - 1)
  | eq A a b => A.bv ⊔ a.bv ⊔ b.bv
  | sigma f | mks f | srec f | wty f | mkw f | wrec f | qty f | mkq f | qrec f => f.bv
  | _ => 0

def bvs : Term Λ → Finset ℕ
  | bound n => {n}
  | trunc A => A.bvs
  | epsilon A => A.bvs
  | dite c t f => c.bvs ∪ (Finset.liftFv t.bvs) ∪ (Finset.liftFv f.bvs)
  | pi A B => A.bvs ∪ (Finset.liftFv B.bvs)
  | app f a => f.bvs ∪ a.bvs
  | abs A t => A.bvs ∪ (Finset.liftFv t.bvs)
  | eq A a b => A.bvs ∪ a.bvs ∪ b.bvs
  | sigma f | mks f | srec f | wty f | mkw f | wrec f | qty f | mkq f | qrec f => f.bvs
  | _ => ∅

theorem mem_bvs_le_bv (n : ℕ) (t : Term Λ) : n ∈ t.bvs → n < t.bv := by
  induction t generalizing n
  <;> simp only [
    bv, bvs,
    Finset.not_mem_empty, Finset.mem_singleton, Finset.mem_union, Finset.mem_liftFv_iff,
    imp_self, not_lt_zero', lt_sup_iff, *]
  case bound => intro h; cases h; simp
  case dite _ _ _ Ic It If =>
    intro h
    casesm* _ ∨ _
    have _ := Ic _ (by assumption); omega
    have _ := It _ (by assumption); omega
    have _ := If _ (by assumption); omega
  case pi _ _ Il Ir => intro h; cases h with
    | inl h => exact Or.inl (Il _ h)
    | inr h => have _ := Ir _ h; omega
  case app _ _ Il Ir => intro h; cases h <;> simp [*]
  case abs _ _ Il Ir => intro h; cases h with
    | inl h => exact Or.inl (Il _ h)
    | inr h => have _ := Ir _ h; omega
  case eq => intro h; casesm* _ ∨ _ <;> simp [*]
  all_goals apply_assumption

def wk (ρ : ℕ → ℕ) : Term Λ → Term Λ
  | bound n => bound (ρ n)
  | trunc A => trunc (A.wk ρ)
  | epsilon A => epsilon (A.wk ρ)
  | dite c t f => dite (c.wk ρ) (t.wk (Nat.liftWk ρ)) (f.wk (Nat.liftWk ρ))
  | pi A B => pi (A.wk ρ) (B.wk (Nat.liftWk ρ))
  | app f a => app (f.wk ρ) (a.wk ρ)
  | abs A t => abs (A.wk ρ) (t.wk (Nat.liftWk ρ))
  | eq A a b => eq (A.wk ρ) (a.wk ρ) (b.wk ρ)
  | sigma f => sigma (f.wk ρ)
  | mks f => mks (f.wk ρ)
  | srec f => srec (f.wk ρ)
  | wty f => wty (f.wk ρ)
  | mkw f => mkw (f.wk ρ)
  | wrec f => wrec (f.wk ρ)
  | qty f => qty (f.wk ρ)
  | mkq f => mkq (f.wk ρ)
  | qrec f => qrec (f.wk ρ)
  | t => t

instance wkSMul : SMul (ℕ → ℕ) (Term Λ) where
  smul := wk

theorem smul_def (ρ : ℕ → ℕ) (t : Term Λ) : ρ • t = t.wk ρ := rfl

@[simp]
theorem wk_id (t : Term Λ) : t.wk id = t := by induction t <;> simp [wk, *]

@[simp]
theorem id_smul (t : Term Λ) : id (α := ℕ) • t = t := wk_id t

theorem wk_liftnWk_ge_bv (ρ : ℕ → ℕ) (n : ℕ) (t : Term Λ) (h : t.bv ≤ n)
  : t.wk (Nat.liftnWk n ρ) = t := by induction t generalizing n ρ with
  | bound k =>
    simp only [bv, wk, Nat.liftnWk, bound.injEq, ite_eq_left_iff, not_lt] at *
    omega
  | _ =>
    simp [wk, bv, <-Nat.liftnWk_succ_apply', *] at * <;>
    (try constructorm* _ ∧ _) <;>
    apply_assumption <;>
    omega

theorem wk_liftnWk_bv (ρ : ℕ → ℕ) (t : Term Λ) : t.wk (Nat.liftnWk t.bv ρ) = t := by
  apply wk_liftnWk_ge_bv
  apply Nat.le_refl

theorem wk_lc (ρ : ℕ → ℕ) (t : Term Λ) (h : t.bv = 0) : t.wk ρ = t := by
  convert wk_liftnWk_bv ρ t
  rw [h, Nat.liftnWk_zero, id]

theorem wk_comp (ρ ρ' : ℕ → ℕ) (t : Term Λ) : t.wk (ρ ∘ ρ') = (t.wk ρ').wk ρ := by
  induction t generalizing ρ ρ' <;> simp [Nat.liftWk_comp, wk, *]

theorem comp_smul (ρ ρ' : ℕ → ℕ) (t : Term Λ) : (ρ ∘ ρ') • t = ρ • ρ' • t := wk_comp ρ ρ' t

abbrev wk0 : Term Λ → Term Λ := wk .succ

@[match_pattern]
def arr : Term Λ → Term Λ → Term Λ := λA B => .pi A (B.wk0)

@[match_pattern]
def neg : Term Λ → Term Λ := λA => .arr A ⊥

-- @[match_pattern]
-- def trunc : Term Λ → Term Λ := λA => .neg (.neg A)

instance fVarToTerm : Coe (FVar Λ) (Term Λ) := ⟨λx => .free x.name x.ty⟩

-- NOTE: all valid terms should satisfy this!
inductive fv_lc : Term Λ → Prop
  | bound {n} : fv_lc (bound n)
  | free {n A} : A.bv = 0 → fv_lc A → fv_lc (free n A)
  | top : fv_lc top
  | bot : fv_lc bot
  | trunc {A} : fv_lc A → fv_lc (trunc A)
  | epsilon {A} : fv_lc A → fv_lc (epsilon A)
  | dite {c t f} : fv_lc c → fv_lc t → fv_lc f → fv_lc (dite c t f)
  | univ {n} : fv_lc (univ n)
  | pi {A B} : fv_lc A → fv_lc B → fv_lc (pi A B)
  | app {f a} : fv_lc f → fv_lc a → fv_lc (app f a)
  | abs {A t} : fv_lc A → fv_lc t → fv_lc (abs A t)
  | eq {A a b} : fv_lc A → fv_lc a → fv_lc b → fv_lc (eq A a b)
  | sigma {f} : fv_lc f → fv_lc (sigma f)
  | mks {f} : fv_lc f → fv_lc (mks f)
  | srec {f} : fv_lc f → fv_lc (srec f)
  | wty {f} : fv_lc f → fv_lc (wty f)
  | mkw {f} : fv_lc f → fv_lc (mkw f)
  | wrec {f} : fv_lc f → fv_lc (wrec f)
  | qty {f} : fv_lc f → fv_lc (qty f)
  | mkq {f} : fv_lc f → fv_lc (mkq f)
  | qrec {f} : fv_lc f → fv_lc (qrec f)
  | invalid : fv_lc invalid

-- TODO: define as actual inductive? or just do induction over?
def valid : Term Λ → Bool
  | free _ A => A.valid ∧ A.bv = 0
  | trunc A => A.valid
  | epsilon A => A.valid
  | dite c t f => c.valid ∧ t.valid ∧ f.valid
  | pi A B => A.valid ∧ B.valid
  | app f a => f.valid ∧ a.valid
  | abs A t => A.valid ∧ t.valid
  | eq A a b => A.valid ∧ a.valid ∧ b.valid
  | sigma f | mks f | srec f | wty f | mkw f | wrec f | qty f | mkq f | qrec f => f.valid
  | invalid => false
  | _ => true

@[simp]
theorem valid_wk_iff {ρ : ℕ → ℕ} {t : Term Λ} : (t.wk ρ).valid ↔ t.valid := by
  induction t generalizing ρ <;> simp [wk, valid, *]

variable [DecidableEq Λ]

def fv : Term Λ → Finset (FVar Λ)
  | free n A => { ⟨n, A⟩ } ∪ A.fv
  | trunc A => A.fv
  | epsilon A => A.fv
  | dite c t f => c.fv ∪ t.fv ∪ f.fv
  | pi A B => A.fv ∪ B.fv
  | app f a => f.fv ∪ a.fv
  | abs A t => A.fv ∪ t.fv
  | eq A a b => A.fv ∪ a.fv ∪ b.fv
  | sigma f | mks f | srec f | wty f | mkw f | wrec f | qty f | mkq f | qrec f => f.fv
  | _ => ∅

@[simp]
theorem fv_coe (x : FVar Λ) : (x : Term Λ).fv = {x} ∪ x.ty.fv := rfl

theorem fv_lc_var' {t : Term Λ} (h : t.fv_lc) : ∀n A, ⟨n, A⟩ ∈ t.fv -> A.bv = 0
  := by intro n A hnA; induction h <;> simp [fv] at * <;> aesop

theorem fv_lc_var {t : Term Λ} (h : t.fv_lc) : ∀x ∈ t.fv, x.ty.bv = 0
  := λx hx => fv_lc_var' h x.name x.ty hx

theorem fv_lc_of_var {t : Term Λ} (h : ∀x ∈ t.fv, x.ty.bv = 0) : t.fv_lc
  := by induction t with
  | free n A IA =>
    constructor
    · apply h ⟨n, A⟩ (by simp [fv])
    · apply IA; intro x hx; apply h; simp [fv, hx]
  | _ => constructor <;> apply_assumption <;> intro x hx <;> apply_assumption <;> simp [fv, *]

theorem fv_lc_of_var' {t : Term Λ} (h : ∀n A, ⟨n, A⟩ ∈ t.fv -> A.bv = 0) : t.fv_lc
  := fv_lc_of_var (λx => h x.name x.ty)

theorem fv_lc_iff (t : Term Λ) : t.fv_lc ↔ ∀x ∈ t.fv, x.ty.bv = 0
  := ⟨fv_lc_var, fv_lc_of_var⟩

theorem fv_lc_iff' (t : Term Λ) : t.fv_lc ↔ (∀n A, ⟨n, A⟩ ∈ t.fv -> A.bv = 0)
  := ⟨fv_lc_var', fv_lc_of_var'⟩

theorem fv_wk (ρ : ℕ → ℕ) (t : Term Λ) : (t.wk ρ).fv = t.fv := by
  induction t generalizing ρ <;> simp [wk, fv, *]
