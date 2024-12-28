import Discretion.Wk.Nat

namespace DLCF

inductive Term : Type
  | bound : ℕ → Term
  | free : ℕ → Term → Term
  | top : Term
  | bot : Term
  | univ : ℕ → Term
  | nil : Term
  | pi : Term → Term → Term
  | app : Term → Term → Term
  | abs : Term → Term → Term
  -- TODO: equality family instead?
  | eq : Term → Term → Term → Term
  deriving DecidableEq

instance : Inhabited Term := ⟨.nil⟩

instance : Top Term := ⟨.top⟩

instance : Bot Term := ⟨.bot⟩

namespace Term

def sexpr : Term → String
  | bound n => "#" ++ toString n
  | free n A => "(" ++ toString n ++ " : " ++ A.sexpr ++ ")"
  | top => "#⊤"
  | bot => "#⊥"
  | univ n => "#U" ++ toString n
  | nil => "()"
  | pi A B => "(#Π " ++ A.sexpr ++ " " ++ B.sexpr ++ ")"
  | app f a => "(" ++ f.sexpr ++ " " ++ a.sexpr ++ ")"
  | abs A t => "(#λ " ++ A.sexpr ++ " " ++ t.sexpr ++ ")"
  | eq A a b => "(#= " ++ A.sexpr ++ " " ++ a.sexpr ++ " " ++ b.sexpr ++ ")"

instance : ToString Term := ⟨sexpr⟩

def depth : Term → ℕ
  | free _ A => A.depth + 1
  | pi A B => (A.depth ⊔ B.depth) + 1
  | app f a => (f.depth ⊔ a.depth) + 1
  | abs A t => (A.depth ⊔ t.depth) + 1
  | eq A a b => (A.depth ⊔ a.depth ⊔ b.depth) + 1
  | _ => 0

def size : Term → ℕ
  | free _ A => A.size + 1
  | pi A B => (A.size + B.size) + 1
  | app f a => (f.size + a.size) + 1
  | abs A t => (A.size + t.size) + 1
  | eq A a b => (A.size + a.size + b.size) + 1
  | _ => 1

theorem depth_lt_size (t : Term) : t.depth < t.size := by
  induction t <;> simp [depth, size, *] <;> omega

def bv : Term → ℕ
  | bound n => n + 1
  | pi A B => A.bv ⊔ (B.bv - 1)
  | app f a => f.bv ⊔ a.bv
  | abs A t => A.bv ⊔ (t.bv - 1)
  | eq A a b => A.bv ⊔ a.bv ⊔ b.bv
  | _ => 0

def wk (ρ : ℕ → ℕ) : Term → Term
  | bound n => bound (ρ n)
  | pi A B => pi (A.wk ρ) (B.wk (Nat.liftWk ρ))
  | app f a => app (f.wk ρ) (a.wk ρ)
  | abs A t => abs (A.wk ρ) (t.wk (Nat.liftWk ρ))
  | eq A a b => eq (A.wk ρ) (a.wk ρ) (b.wk ρ)
  | t => t

instance wkSMul : SMul (ℕ → ℕ) Term where
  smul := wk

theorem smul_def (ρ : ℕ → ℕ) (t : Term) : ρ • t = t.wk ρ := rfl

@[simp]
theorem wk_id (t : Term) : t.wk id = t := by induction t <;> simp [wk, *]

@[simp]
theorem id_smul (t : Term) : id (α := ℕ) • t = t := wk_id t

theorem wk_liftnWk_ge_bv (ρ : ℕ → ℕ) (n : ℕ) (t : Term) (h : t.bv ≤ n)
  : t.wk (Nat.liftnWk n ρ) = t := by induction t generalizing n ρ with
  | bound k =>
    simp only [bv, wk, Nat.liftnWk, bound.injEq, ite_eq_left_iff, not_lt] at *
    omega
  | _ =>
    simp [wk, bv, <-Nat.liftnWk_succ_apply', *] at * <;>
    (try constructorm* _ ∧ _) <;>
    apply_assumption <;>
    omega

theorem wk_liftnWk_bv (ρ : ℕ → ℕ) (t : Term) : t.wk (Nat.liftnWk t.bv ρ) = t := by
  apply wk_liftnWk_ge_bv
  apply Nat.le_refl

theorem wk_lc (ρ : ℕ → ℕ) (t : Term) (h : t.bv = 0) : t.wk ρ = t := by
  convert wk_liftnWk_bv ρ t
  rw [h, Nat.liftnWk_zero, id]

theorem wk_comp (ρ ρ' : ℕ → ℕ) (t : Term) : t.wk (ρ ∘ ρ') = (t.wk ρ').wk ρ := by
  induction t generalizing ρ ρ' <;> simp [Nat.liftWk_comp, wk, *]

theorem comp_smul (ρ ρ' : ℕ → ℕ) (t : Term) : (ρ ∘ ρ') • t = ρ • ρ' • t := wk_comp ρ ρ' t

abbrev wk0 : Term → Term := wk .succ

@[match_pattern]
def arr : Term → Term → Term := λA B => .pi A (B.wk0)

@[match_pattern]
def neg : Term → Term := λA => .arr A ⊥

@[match_pattern]
def trunc : Term → Term := λA => .neg (.neg A)

structure FVar where
  name : ℕ
  ty : Term
  deriving DecidableEq

instance fVarToTerm : Coe FVar Term := ⟨λx => .free x.name x.ty⟩

def fv : Term → Finset FVar
  | free n A => { ⟨n, A⟩ } ∪ A.fv
  | pi A B => A.fv ∪ B.fv
  | app f a => f.fv ∪ a.fv
  | abs A t => A.fv ∪ t.fv
  | eq A a b => A.fv ∪ a.fv ∪ b.fv
  | _ => ∅

@[simp]
theorem fv_coe (x : FVar) : (x : Term).fv = {x} ∪ x.ty.fv := rfl

-- NOTE: all valid terms should satisfy this!
inductive fv_lc : Term → Prop
  | bound {n} : fv_lc (bound n)
  | free {n A} : A.bv = 0 → fv_lc A → fv_lc (free n A)
  | top : fv_lc top
  | bot : fv_lc bot
  | univ {n} : fv_lc (univ n)
  | nil : fv_lc nil
  | pi {A B} : fv_lc A → fv_lc B → fv_lc (pi A B)
  | app {f a} : fv_lc f → fv_lc a → fv_lc (app f a)
  | abs {A t} : fv_lc A → fv_lc t → fv_lc (abs A t)
  | eq {A a b} : fv_lc A → fv_lc a → fv_lc b → fv_lc (eq A a b)

theorem fv_lc_var' {t : Term} (h : t.fv_lc) : ∀n A, ⟨n, A⟩ ∈ t.fv -> A.bv = 0
  := by intro n A hnA; induction h <;> simp [fv] at * <;> aesop

theorem fv_lc_var {t : Term} (h : t.fv_lc) : ∀x ∈ t.fv, x.ty.bv = 0
  := λx hx => fv_lc_var' h x.name x.ty hx

theorem fv_lc_of_var {t : Term} (h : ∀x ∈ t.fv, x.ty.bv = 0) : t.fv_lc
  := by induction t with
  | free n A IA =>
    constructor
    · apply h ⟨n, A⟩ (by simp [fv])
    · apply IA; intro x hx; apply h; simp [fv, hx]
  | _ => constructor <;> apply_assumption <;> intro x hx <;> apply_assumption <;> simp [fv, *]

theorem fv_lc_of_var' {t : Term} (h : ∀n A, ⟨n, A⟩ ∈ t.fv -> A.bv = 0) : t.fv_lc
  := fv_lc_of_var (λx => h x.name x.ty)

theorem fv_lc_iff (t : Term) : t.fv_lc ↔ ∀x ∈ t.fv, x.ty.bv = 0
  := ⟨fv_lc_var, fv_lc_of_var⟩

theorem fv_lc_iff' (t : Term) : t.fv_lc ↔ (∀n A, ⟨n, A⟩ ∈ t.fv -> A.bv = 0)
  := ⟨fv_lc_var', fv_lc_of_var'⟩

theorem fv_wk (ρ : ℕ → ℕ) (t : Term) : (t.wk ρ).fv = t.fv := by
  induction t generalizing ρ <;> simp [wk, fv, *]
