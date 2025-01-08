import DLCF.Typing.Basic

namespace DLCF

namespace Term

variable {Λ} [DecidableEq Λ] [Level Λ] [maxU : LevelBound Λ]

structure FSubst.JEq (Γ Δ : Finset (FVar Λ)) (σ σ' : FSubst Λ) : Prop where
  okIn : Ok Γ
  jeq : ∀x ∈ Δ, Γ ⊢ σ x ≡ σ' x : x.ty

notation Γ " ⊢ " a " ≡ " b " ▷ " Δ => FSubst.JEq Γ Δ a b

theorem FSubst.JEq.symm {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} (h : Γ ⊢ σ ≡ σ' ▷ Δ)
  : Γ ⊢ σ' ≡ σ ▷ Δ where
  okIn := h.okIn
  jeq x hx := (h.jeq x hx).symm

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

theorem FSubst.JEq.insert {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ Δ) (hx : Γ ⊢ σ x ≡ σ' x : x.ty) : Γ ⊢ σ ≡ σ' ▷ insert x Δ where
  okIn := h.okIn
  jeq y hy := if hxy : y = x then hxy ▸ hx else h.jeq y (Finset.mem_of_mem_insert_of_ne hy hxy)

theorem FSubst.JEq.insert_jeq {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ (Insert.insert x Δ)) : Γ ⊢ σ x ≡ σ' x : x.ty
  := h.jeq x (Finset.mem_insert_self x Δ)

theorem FSubst.JEq.insert_rest {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ (Insert.insert x Δ)) : Γ ⊢ σ ≡ σ' ▷ Δ := h.wkOut (Finset.subset_insert x Δ)

theorem FSubst.JEq.insert_iff {Γ Δ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  : (Γ ⊢ σ ≡ σ' ▷ (Insert.insert x Δ)) ↔ (Γ ⊢ σ x ≡ σ' x : x.ty) ∧ (Γ ⊢ σ ≡ σ' ▷ Δ)
  := ⟨λh => ⟨h.insert_jeq, h.insert_rest⟩, λ⟨h, h'⟩ => h'.insert h⟩

-- TODO: add induction principle for FSubst...

-- TODO: insert set, based on ⊥ and friends...

theorem FSubst.JEq.singleton {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ x ≡ σ' x : x.ty) : Γ ⊢ σ ≡ σ' ▷ {x} := (empty h.ok).insert h

theorem FSubst.JEq.singleton_jeq {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ {x}) : Γ ⊢ σ x ≡ σ' x : x.ty := h.jeq x (Finset.mem_singleton_self x)

theorem FSubst.JEq.singleton_iff {Γ : Finset (FVar Λ)} {σ σ' : FSubst Λ} {x : FVar Λ}
  : (Γ ⊢ σ ≡ σ' ▷ {x}) ↔ (Γ ⊢ σ x ≡ σ' x : x.ty) := ⟨singleton_jeq, singleton⟩

theorem FSubst.JEq.union {Γ Δ Δ' : Finset (FVar Λ)} {σ σ' : FSubst Λ}
  (h : Γ ⊢ σ ≡ σ' ▷ Δ) (h' : Γ ⊢ σ ≡ σ' ▷ Δ') : Γ ⊢ σ ≡ σ' ▷ Δ ∪ Δ' where
  okIn := h.okIn
  jeq x hx := by
    simp only [Finset.mem_union] at hx; cases hx
    · apply h.jeq; assumption
    · apply h'.jeq; assumption

theorem FSubst.JEq.left_congr_trg {Γ Δ : Finset (FVar Λ)} {σ σ' τ : FSubst Λ}
  (hσ : ∀x ∈ Δ, σ x = τ x) (h : Γ ⊢ σ ≡ σ' ▷ Δ) : Γ ⊢ τ ≡ σ' ▷ Δ where
  okIn := h.okIn
  jeq x hx := hσ x hx ▸ h.jeq x hx

theorem FSubst.JEq.right_congr_trg {Γ Δ : Finset (FVar Λ)} {σ σ' τ : FSubst Λ}
  (hσ' : ∀x ∈ Δ, σ' x = τ x) (h : Γ ⊢ σ ≡ σ' ▷ Δ) : Γ ⊢ σ ≡ τ ▷ Δ where
  okIn := h.okIn
  jeq x hx := hσ' x hx ▸ h.jeq x hx

structure FSubst.Wf (Γ Δ : Finset (FVar Λ)) (σ : FSubst Λ) : Prop where
  okIn : Ok Γ
  okOut : Ok Δ
  wf : ∀x ∈ Δ, Γ ⊢ σ x : x.ty

notation Γ " ⊢ " a " ▷ " Δ => FSubst.Wf Γ Δ a

theorem FSubst.Wf.refl {Γ Δ : Finset (FVar Λ)} {σ : FSubst Λ} (h : Γ ⊢ σ ▷ Δ)
  : Γ ⊢ σ ≡ σ ▷ Δ where
  okIn := h.okIn
  jeq x hx := (h.wf x hx).refl
