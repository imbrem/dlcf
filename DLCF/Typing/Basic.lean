import DLCF.Syntax.Subst

namespace DLCF

def imax (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => n ⊔ (m + 1)

namespace Term

inductive JEq : Finset FVar → Term → Term → Term → Prop
  | nil_ok : JEq ∅ ⊤ .nil .nil
  | cons_ok (hA : JEq Γ (.univ n) A A) : JEq (insert ⟨i, A⟩ Γ) ⊤ .nil .nil
  | var (hΓ : JEq Γ ⊤ .nil .nil) (hx : ⟨i, A⟩ ∈ Γ) : JEq Γ A (.free i A) (.free i A)
  | top (hΓ : JEq Γ ⊤ .nil .nil) : JEq Γ (.univ 0) .top .top
  | bot (hΓ : JEq Γ ⊤ .nil .nil) : JEq Γ (.univ 0) .bot .bot
  | univ (hΓ : JEq Γ ⊤ .nil .nil) : JEq Γ (.univ (n + 1)) (.univ n) (.univ n)
  -- TODO: swap from cofinite quantification to universal?
  | pi (L : Finset FVar) (x) (hx : x ∉ L)
    (hA : JEq Γ (.univ n) A A')
    (hB : JEq (insert x Γ) (.univ m) (b0 x • B) (b0 x • B'))
    : JEq Γ (.univ (imax n m)) (.pi A B) (.pi A' B')
  | app (hf : JEq Γ (.pi A B) f f') (ha : JEq Γ A a a') : JEq Γ (b0 a • B) (.app f a) (.app f' a')
  | abs (L : Finset FVar) (x) (hx : x ∉ L)
    (hA : JEq Γ (.univ n) A A')
    (ht : JEq (insert x Γ) (b0 x • B) (b0 x • t) (b0 x • t'))
    : JEq Γ (.pi A B) (.abs A t) (.abs A' t')
  | eq
    (hA : JEq Γ (.univ n) A A')
    (ha : JEq Γ A a a')
    (hb : JEq Γ A' b b')
    : JEq Γ (.univ 0) (.eq A a b) (.eq A' a' b')
  | eq_rfl (jab : JEq Γ A a b) : JEq Γ (.eq A a b) .nil .nil
  -- Extensionality
  | jeq_ext (eab : JEq Γ (.eq A a b) .nil .nil) : JEq Γ A a b
  -- Propositional extensionality
  | u0_ext
    (hA : JEq Γ (.univ 0) A A)
    (hB : JEq Γ (.univ 0) B B)
    (hAB : JEq Γ (.arr A B) .nil .nil)
    (hBA : JEq Γ (.arr B A) .nil .nil)
    : JEq Γ (.univ 0) A B
  -- Propositional irrelevance
  | u0_irr (hA : JEq Γ (.univ 0) A A) (ha : JEq Γ A a a) : JEq Γ A a .nil
  -- Double negation elimination
  | dne (hA : JEq Γ (.univ 0) A A) (hna : JEq Γ (.neg (.neg A)) .nil .nil) : JEq Γ A .nil .nil
  -- The axiom of choice
  | aoc (hf : JEq Γ (.pi A (.trunc B)) .nil .nil) : JEq Γ (.trunc (.pi A B)) .nil .nil
  | symm : JEq Γ A a b → JEq Γ A b a
  | cast : JEq Γ (.univ n) A B → JEq Γ A a b → JEq Γ B a b
  | trans : JEq Γ A a b → JEq Γ A b c → JEq Γ A a c

notation Γ " ⊢ " a " ≡ " b " : " A => JEq Γ A a b

notation Γ " ⊢ " a " : " A => Γ ⊢ a ≡ a : A

notation Γ " ok" => Γ ⊢ Term.nil : ⊤

theorem JEq.cons_ok' (x : FVar) (hA : Γ ⊢ x.ty : .univ n) : (insert x Γ) ok
  := by cases x; exact .cons_ok hA

theorem JEq.u0_jeq (hA : Γ ⊢ A : .univ 0) (hp : Γ ⊢ p : A) (hq : Γ ⊢ q : A) : Γ ⊢ p ≡ q : A
  := .trans (.u0_irr hA hp) (.symm (.u0_irr hA hq))

theorem JEq.ctx_ok (h : Γ ⊢ a ≡ b : A) : Γ ok := by induction h with
  | nil_ok => exact .nil_ok
  | cons_ok hA => exact .cons_ok hA
  | _ => assumption

-- TODO: existential introduction rules

-- TODO: universal elimination rules (?)

-- TODO: lore about universes, regularity, and other such nonsense

abbrev Wf (Γ : Finset FVar) (A : Term) := {t : Term // Γ ⊢ t : A}

instance Wf.setoid (Γ : Finset FVar) (A : Term) : Setoid (Term.Wf Γ A) where
  r s t := Γ ⊢ s.val ≡ t.val : A
  iseqv := {
    refl x := x.prop,
    symm h := .symm h,
    trans h h' := .trans h h'
  }

-- TODO: constructors for Wf

-- TODO: congruence theorems for Wf

abbrev Eqv (Γ : Finset FVar) (A : Term) := Quotient (Wf.setoid Γ A)

-- TODO: constructors for Eqv
