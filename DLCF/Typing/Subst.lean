import DLCF.Typing.Basic

namespace DLCF

namespace Term

variable {Λ} [DecidableEq Λ] [Level Λ] [maxU : LevelBound Λ]

structure FSubst.JEq (Γ Δ : Finset (FVar Λ)) (σ σ' : FSubst Λ) : Prop where
  okIn : Ok Γ
  jeq : ∀x ∈ Δ, Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ

notation Γ " ⊢ " a " ≡ " b " ▷ " Δ => FSubst.JEq Γ Δ a b

-- TODO: proving this requires regularity ... or do we do the HEq trick?
-- _or_ can prove jeq_right by induction?
-- theorem FSubst.JEq.symm {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} (h : Γ ⊢ σ ≡ σ' ▷ Δ)
--   : Γ ⊢ σ' ≡ σ ▷ Δ where
--   okIn := h.okIn
--   jeq x hx := (h.jeq x hx).symm

theorem FSubst.JEq.trans {Γ Δ : Finset (FVar Λ)} {σ σ' σ'' : FSubst Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ Δ) (h' : Γ ⊢ σ' ≡ σ'' ▷ Δ) : Γ ⊢ σ ≡ σ'' ▷ Δ where
  okIn := h.okIn
  jeq x hx := (h.jeq x hx).trans (h'.jeq x hx)

theorem FSubst.JEq.wkIn {Γ Γ' Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ}
  (hΓ : Ok Γ) (w : Γ' ⊆ Γ) (h : Γ' ⊢ σ ≡ σ' ▷ Δ) : Γ ⊢ σ ≡ σ' ▷ Δ where
  okIn := hΓ
  jeq x hx := (h.jeq x hx).wk hΓ w

theorem FSubst.JEq.wkOut {Γ Δ Δ' : Finset (FVar Λ)} {σ σ' : FSubst Λ}
  (w : Δ' ⊆ Δ) (h : Γ ⊢ σ ≡ σ' ▷ Δ) : Γ ⊢ σ ≡ σ' ▷ Δ' where
  okIn := h.okIn
  jeq x hx := h.jeq x (w hx)

theorem FSubst.JEq.empty {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} (hΓ : Ok Γ)
  : Γ ⊢ σ ≡ σ' ▷ ∅ where
  okIn := hΓ
  jeq x hx := absurd hx (Finset.not_mem_empty x)

@[simp]
theorem FSubst.JEq.empty_iff {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ}
  : (Γ ⊢ σ ≡ σ' ▷ ∅) ↔ Ok Γ := ⟨λh => h.okIn, λh => empty h⟩

theorem FSubst.JEq.insertIn {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ}
  (hA : Γ ⊢ A ≡ A : .univ n) (h : Γ ⊢ σ ≡ σ' ▷ Δ) : (insert ⟨i, A⟩ Γ) ⊢ σ ≡ σ' ▷ Δ where
  okIn := hA.ok_var i
  jeq y hy := (h.jeq y hy).wki hA

theorem FSubst.JEq.insertOut {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ Δ) (hx : Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ) : Γ ⊢ σ ≡ σ' ▷ insert x Δ where
  okIn := h.okIn
  jeq y hy := if hxy : y = x then hxy ▸ hx else h.jeq y (Finset.mem_of_mem_insert_of_ne hy hxy)

theorem FSubst.JEq.insertOut_jeq {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ (Insert.insert x Δ)) : Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ
  := h.jeq x (Finset.mem_insert_self x Δ)

theorem FSubst.JEq.insertOut_rest {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ (Insert.insert x Δ)) : Γ ⊢ σ ≡ σ' ▷ Δ := h.wkOut (Finset.subset_insert x Δ)

theorem FSubst.JEq.insertOut_iff {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  : (Γ ⊢ σ ≡ σ' ▷ (Insert.insert x Δ)) ↔ (Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ) ∧ (Γ ⊢ σ ≡ σ' ▷ Δ)
  := ⟨λh => ⟨h.insertOut_jeq, h.insertOut_rest⟩, λ⟨h, h'⟩ => h'.insertOut h⟩

-- theorem JEq.subst {Γ Δ : Finset (FVar Λ)} (hσ : Γ ⊢ σ ≡ σ' ▷ Δ) (ha : Δ ⊢ a ≡ a' : A)
--   : Γ ⊢ a.fsubst σ ≡ a'.fsubst σ' : A.fsubst σ := by induction ha with
--   | top_emp => exact hσ.okIn.top
--   | top_cons => exact hσ.okIn.top
--   | var hA hx IA => exact hσ.jeq _ hx
--   | bot => exact hσ.okIn.bot
--   | tt => exact hσ.okIn.tt
--   | dite hφ ht hf Iφ It If =>
--     apply JEq.dite (Iφ hσ)
--     sorry
--     sorry
--   | _ =>
--     constructor
--     <;> sorry

-- TODO: add induction principle for FSubst...

-- TODO: insert set, based on ⊥ and friends...

theorem FSubst.JEq.singleton {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ) : Γ ⊢ σ ≡ σ' ▷ {x} := (empty h.ok).insertOut h

theorem FSubst.JEq.singleton_jeq {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ {x}) : Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ := h.jeq x (Finset.mem_singleton_self x)

theorem FSubst.JEq.singleton_iff {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  : (Γ ⊢ σ ≡ σ' ▷ {x}) ↔ (Γ ⊢ σ x ≡ σ' x : x.ty.fsubst σ) := ⟨singleton_jeq, singleton⟩

theorem FSubst.JEq.union {Γ Δ Δ' : Finset (FVar Λ)} {σ σ' : FSubst Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ Δ) (h' : Γ ⊢ σ ≡ σ' ▷ Δ') : Γ ⊢ σ ≡ σ' ▷ Δ ∪ Δ' where
  okIn := h.okIn
  jeq x hx := by
    simp only [Finset.mem_union] at hx; cases hx
    · apply h.jeq; assumption
    · apply h'.jeq; assumption

-- TODO: need regularity for this too, unless, again, HEq trick
-- theorem FSubst.JEq.left_congr_trg {Γ Δ : Finset (FVar Λ)} {σ σ' τ : FSubst Λ}
--   (hσ : ∀x ∈ Δ, σ x = τ x) (h : Γ ⊢ σ ≡ σ' ▷ Δ) : Γ ⊢ τ ≡ σ' ▷ Δ where
--   okIn := h.okIn
--   jeq x hx := hσ x hx ▸ h.jeq x hx

theorem FSubst.JEq.right_congr_trg {Γ Δ : Finset (FVar Λ)} {σ σ' τ : FSubst Λ}
  (hσ' : ∀x ∈ Δ, σ' x = τ x) (h : Γ ⊢ σ ≡ σ' ▷ Δ) : Γ ⊢ σ ≡ τ ▷ Δ where
  okIn := h.okIn
  jeq x hx := hσ' x hx ▸ h.jeq x hx

structure FSubst.Wf (Γ Δ : Finset (FVar Λ)) (σ : FSubst Λ) : Prop where
  okIn : Ok Γ
  okOut : Ok Δ
  wf : ∀x ∈ Δ, Γ ⊢ σ x : x.ty.fsubst σ

notation Γ " ⊢ " a " ▷ " Δ => FSubst.Wf Γ Δ a

theorem FSubst.Wf.refl {Γ Δ : Finset (FVar Λ)} {σ : FSubst Λ} (h : Γ ⊢ σ ▷ Δ)
  : Γ ⊢ σ ≡ σ ▷ Δ where
  okIn := h.okIn
  jeq x hx := (h.wf x hx).refl
