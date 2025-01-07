import DLCF.Syntax.BSubst
import DLCF.Syntax.FSubst

namespace DLCF

namespace Term

variable {Λ}

def FSubst.bsubst (τ : BSubst Λ) (σ : FSubst Λ) : FSubst Λ := λx => τ • (σ x)

@[simp]
theorem FSubst.bsubst_applied (τ : BSubst Λ) (σ : FSubst Λ) (x)
  : (σ.bsubst τ) x = τ • (σ x) := rfl

@[simp]
theorem FSubst.bsubst_one (σ : FSubst Λ) : σ.bsubst 1 = σ := by funext x; simp

theorem FSubst.bsubst_mul (τ ρ : BSubst Λ) (σ : FSubst Λ) : (σ.bsubst (τ * ρ)) = (σ.bsubst ρ).bsubst τ
  := by funext x; simp [mul_smul]

@[simp]
theorem FSubst.bsubst_id (σ : FSubst Λ) : σ.bsubst BSubst.id = σ := bsubst_one σ

theorem FSubst.bsubst_comp (τ ρ : BSubst Λ) (σ : FSubst Λ)
  : (σ.bsubst (τ.comp ρ)) = (σ.bsubst ρ).bsubst τ
  := bsubst_mul τ ρ σ

instance FSubst.mulActionFSubst : MulAction (BSubst Λ) (FSubst Λ) where
  smul := bsubst
  one_smul := bsubst_one
  mul_smul := bsubst_mul
