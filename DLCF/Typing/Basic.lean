import DLCF.Syntax.Subst

namespace DLCF

def imax (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => n ⊔ (m + 1)

namespace Term

inductive JEq : Finset FVar → Term → Term → Term → Prop
  | nil_ok : JEq ∅ ⊤ .nil .nil
  | cons_ok (hA : JEq Γ (.univ n) A A) : JEq (insert ⟨i, A⟩ Γ) ⊤ .nil .nil
  | var (hΓ : JEq Γ (.univ n) A A) (hx : ⟨i, A⟩ ∈ Γ) : JEq Γ A (.free i A) (.free i A)
  | top (hΓ : JEq Γ ⊤ .nil .nil) : JEq Γ (.univ 0) .top .top
  | bot (hΓ : JEq Γ ⊤ .nil .nil) : JEq Γ (.univ 0) .bot .bot
  | univ (hΓ : JEq Γ ⊤ .nil .nil) : JEq Γ (.univ (n + 1)) (.univ n) (.univ n)
  -- TODO: swap from cofinite quantification to universal?
  | pi
    (hA : JEq Γ (.univ n) A A')
    (hx : ⟨i, A⟩ ∉ Γ ∪ fv B)
    (hB : JEq (insert ⟨i, A⟩ Γ) (.univ m) (b0 (.free i A) • B) (b0 (.free i A) • B'))
    : JEq Γ (.univ (imax n m)) (.pi A B) (.pi A' B')
  | app (hf : JEq Γ (.pi A B) f f') (ha : JEq Γ A a a') : JEq Γ (b0 a • B) (.app f a) (.app f' a')
  | abs
    (hA : JEq Γ (.univ n) A A')
    (hx : ⟨i, A⟩ ∉ Γ ∪ fv t)
    (ht : JEq (insert ⟨i, A⟩ Γ) (b0 (.free i A) • B) (b0 (.free i A) • t) (b0 (.free i A) • t'))
    : JEq Γ (.pi A B) (.abs A t) (.abs A' t')
  | eq
    (hA : JEq Γ (.univ n) A A')
    (ha : JEq Γ A a a')
    (hb : JEq Γ A b b')
    : JEq Γ (.univ 0) (.eq A a b) (.eq A' a' b')
  | eq_rfl (jab : JEq Γ A a b) : JEq Γ (.eq A a b) .nil .nil
  -- β-reduction
  | β_abs
    (h : JEq Γ B l (.app (.abs A t) r)) : JEq Γ B l (b0 r • t)
  -- η-expansion
  | η_abs (h : JEq Γ (.pi A B) l r) : JEq Γ (.pi A B) l (.abs A (.app r (.bound 0)))
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
  -- TODO: generalize to truncation elimination
  | dne (hA : JEq Γ (.univ 0) A A) (hna : JEq Γ (.neg (.neg A)) .nil .nil) : JEq Γ A .nil .nil
  -- The axiom of choice
  | aoc (hf : JEq Γ (.pi A (.trunc B)) .nil .nil) : JEq Γ (.trunc (.pi A B)) .nil .nil
  | symm : JEq Γ A a b → JEq Γ A b a
  | cast : JEq Γ (.univ n) A B → JEq Γ A a b → JEq Γ B a b
  | trans : JEq Γ A a b → JEq Γ A b c → JEq Γ A a c

attribute [simp] JEq.nil_ok

notation Γ " ⊢ " a " ≡ " b " : " A => JEq Γ A a b

theorem JEq.to_nil (h : Γ ⊢ a ≡ b : A) : Γ ⊢ .nil ≡ .nil : ⊤ := by induction h with
  | nil_ok => exact .nil_ok
  | cons_ok hA => exact .cons_ok hA
  | _ => assumption

-- notation Γ " ok" => Γ ⊢ Term.nil : ⊤

inductive HasTy : Finset FVar → Term → Term → Prop
  | nil_ok : HasTy ∅ ⊤ .nil
  | cons_ok (hA : HasTy Γ (.univ n) A) : HasTy (insert ⟨i, A⟩ Γ) ⊤ .nil
  | var (hΓ : HasTy Γ (.univ n) A) (hx : ⟨i, A⟩ ∈ Γ) : HasTy Γ A (.free i A)
  | top (hΓ : HasTy Γ ⊤ .nil) : HasTy Γ (.univ 0) ⊤
  | bot (hΓ : HasTy Γ ⊤ .nil) : HasTy Γ (.univ 0) .bot
  | univ (hΓ : HasTy Γ ⊤ .nil) : HasTy Γ (.univ (n + 1)) (.univ n)
  | pi
    (hA : HasTy Γ (.univ n) A)
    (hx : ⟨i, A⟩ ∉ Γ ∪ fv B)
    (hB : HasTy (insert ⟨i, A⟩ Γ) (.univ m) (b0 (.free i A) • B))
    : HasTy Γ (.univ (imax n m)) (.pi A B)
  | app (hf : HasTy Γ (.pi A B) f) (ha : HasTy Γ A a) : HasTy Γ (b0 a • B) (.app f a)
  | abs
    (hA : HasTy Γ (.univ n) A)
    (hx : ⟨i, A⟩ ∉ Γ ∪ fv t)
    (ht : HasTy (insert ⟨i, A⟩ Γ) (b0 (.free i A) • B) (b0 (.free i A) • t))
    : HasTy Γ (.pi A B) (.abs A t)
  | eq
    (hA : HasTy Γ (.univ n) A)
    (ha : HasTy Γ A a)
    (hb : HasTy Γ A b)
    : HasTy Γ (.univ 0) (.eq A a b)
  | eq_rfl (h : Γ ⊢ a ≡ b : A) : HasTy Γ (.eq A a b) .nil
  | cast (h : Γ ⊢ A ≡ B : .univ n) (ha : HasTy Γ A a) : HasTy Γ B a

notation Γ " ⊢ " a " : " A => HasTy Γ A a

theorem HasTy.refl {Γ A a} (h : Γ ⊢ a : A) : Γ ⊢ a ≡ a : A := by induction h with
  | cast h ha Ia => exact .cast h Ia
  | _ => constructor <;> (try apply JEq.to_nil) <;> assumption

-- theorem JEq.left_eq_helper {Γ A a} (h : Γ ⊢ a ≡ b : A) (hab : a = b) : Γ ⊢ a : A := by
--   induction h with
--   | β_abs => sorry -- TODO: needs inversion + substitution
--   | η_abs => sorry
--   | jeq_ext => sorry
--   | u0_ext => sorry
--   | u0_irr => sorry
--   | dne => sorry
--   | aoc => sorry
--   | symm => sorry
--   | cast => sorry
--   | trans => sorry
--   | _ => cases hab; constructor <;> apply_assumption <;> rfl

-- theorem JEq.left {Γ A a} (h : Γ ⊢ a ≡ b : A) : Γ ⊢ a : A := by
  -- induction h with
  -- | pi => sorry
  -- | abs => sorry
  -- | app => sorry
  -- | eq hA ha hb IA Ia Ib => exact ⟨.eq IA.left Ia.left Ib.left, .eq IA.right (Ia.left.cast IA) sorry⟩
  -- | eq_rfl => sorry
  -- | β_abs => sorry
  -- | η_abs => sorry
  -- | jeq_ext => sorry
  -- | u0_ext => sorry
  -- | u0_irr => sorry
  -- | dne => sorry
  -- | aoc => sorry
  -- | symm => sorry
  -- | cast => sorry
  -- | trans => sorry
  -- | _ =>
  --   (try casesm* _ ∧ _)
  --   constructor
  --   · constructor <;> assumption
  --   · constructor <;> assumption

-- inductive CtxOk : Finset FVar → Prop
--   | nil_ok : CtxOk ∅
--   | cons_ok {Γ i A} (hΓ : CtxOk Γ) (hA : Γ ⊢ A : .univ n) : CtxOk (insert ⟨i, A⟩ Γ)

-- attribute [simp] CtxOk.nil_ok

-- theorem CtxOk.jeq_nil {Γ} (hΓ : CtxOk Γ) : Γ ⊢ .nil : ⊤ := by induction hΓ with
--   | nil_ok => exact .nil_ok
--   | cons_ok hΓ hA => exact .cons_ok hA

-- theorem CtxOk.of_jeq_nil {Γ} (hΓ : Γ ⊢ .nil : ⊤) : CtxOk Γ := by
--   generalize ht : (⊤ : Term) = t at hΓ
--   generalize hn : Term.nil = n at hΓ
--   sorry

-- theorem CtxOk.iff_jeq_nil {Γ} : CtxOk Γ ↔ Γ ⊢ .nil : ⊤ := by induction Γ using Finset.induction with
--   | empty => simp
--   | insert hx Ih =>
--     rename_i x Γ
--     cases x with | mk i A =>
--     constructor
--     · intro hΓ
--       sorry
--     · sorry

-- theorem JEq.left_wf (h : Γ ⊢ a ≡ b : A) : Γ ⊢ a : A := .trans h (.symm h)

-- theorem JEq.right_wf (h : Γ ⊢ a ≡ b : A) : Γ ⊢ b : A := .trans (.symm h) h

-- theorem JEq.cons_ok' (x : FVar) (hA : Γ ⊢ x.ty : .univ n) : (insert x Γ) ok
--   := by cases x; exact .cons_ok hA

-- theorem JEq.u0_jeq (hA : Γ ⊢ A : .univ 0) (hp : Γ ⊢ p : A) (hq : Γ ⊢ q : A) : Γ ⊢ p ≡ q : A
--   := .trans (.u0_irr hA hp) (.symm (.u0_irr hA hq))


-- def IsTy (Γ : Finset FVar) (A : Term) := ∃n, Γ ⊢ A : .univ n

-- notation Γ " ⊢ " A " isty" => IsTy Γ A

-- theorem IsTy.top {Γ : Finset FVar} (h : Γ ok) : Γ ⊢ .top isty := ⟨0, .top h⟩

-- theorem IsTy.bot {Γ : Finset FVar} (h : Γ ok) : Γ ⊢ .bot isty := ⟨0, .bot h⟩

-- theorem IsTy.univ {n} {Γ : Finset FVar} (h : Γ ok) : Γ ⊢ .univ n isty := ⟨n + 1, .univ h⟩

-- theorem IsTy.pi {Γ : Finset FVar} {A B}
--    (hA : Γ ⊢ A isty)
--    (hx : ⟨i, A⟩ ∉ Γ ∪ fv B)
--    (hB : insert ⟨i, A⟩ Γ ⊢ b0 (.free i A) • B isty)
--   : Γ ⊢ .pi A B isty
--   := have ⟨_, hA⟩ := hA; have ⟨_, hB⟩ := hB; ⟨_, .pi hA hx hB⟩

-- @[match_pattern]
-- theorem IsTy.eq {Γ : Finset FVar} {A a b} (hA : Γ ⊢ A isty) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : A)
--   : Γ ⊢ .eq A a b isty := have ⟨_, hA⟩ := hA; ⟨0, .eq hA ha hb⟩

-- theorem JEq.regular (h : Γ ⊢ a ≡ b : A) : Γ ⊢ A isty := by induction h with
--   | nil_ok => exact .top .nil_ok
--   | cons_ok hA => exact .top (.cons_ok hA)
--   | _ => sorry

-- -- TODO: existential introduction rules

-- -- TODO: universal elimination rules (?)

-- -- TODO: lore about universes, regularity, and other such nonsense

-- abbrev Wf (Γ : Finset FVar) (A : Term) := {t : Term // Γ ⊢ t : A}

-- instance Wf.setoid (Γ : Finset FVar) (A : Term) : Setoid (Term.Wf Γ A) where
--   r s t := Γ ⊢ s.val ≡ t.val : A
--   iseqv := {
--     refl x := x.prop,
--     symm h := .symm h,
--     trans h h' := .trans h h'
--   }

-- -- TODO: constructors for Wf

-- -- TODO: congruence theorems for Wf

-- abbrev Eqv (Γ : Finset FVar) (A : Term) := Quotient (Wf.setoid Γ A)

-- TODO: constructors for Eqv
