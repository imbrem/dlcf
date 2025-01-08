import DLCF.Syntax.Basic

namespace DLCF

namespace Term

variable {Λ}

def usubst (μ : Λ → Λ') : Term Λ → Term Λ'
  | bound n => bound n
  | free n t => free n (t.usubst μ)
  | top => top
  | bot => bot
  | trunc A => trunc (A.usubst μ)
  | epsilon A => epsilon (A.usubst μ)
  | univ ℓ => univ (μ ℓ)
  | dite c t f => dite (c.usubst μ) (t.usubst μ) (f.usubst μ)
  | pi A B => pi (A.usubst μ) (B.usubst μ)
  | app f a => app (f.usubst μ) (a.usubst μ)
  | abs A t => abs (A.usubst μ) (t.usubst μ)
  | eq A a b => eq (A.usubst μ) (a.usubst μ) (b.usubst μ)
  | sigma f => sigma (f.usubst μ)
  | mks f => mks (f.usubst μ)
  | srec f => srec (f.usubst μ)
  | wty f => wty (f.usubst μ)
  | mkw f => mkw (f.usubst μ)
  | wrec f => wrec (f.usubst μ)
  | qty f => qty (f.usubst μ)
  | mkq f => mkq (f.usubst μ)
  | qrec f => qrec (f.usubst μ)
  | invalid => invalid

@[simp]
theorem usubst_id (t : Term Λ) : t.usubst id = t := by induction t <;> simp [usubst, *]

theorem usubst_comp (μ : Λ → Λ') (ν : Λ' → Λ'') (t : Term Λ)
  : t.usubst (ν ∘ μ) = (t.usubst μ).usubst ν := by induction t <;> simp [usubst, *]

class LevelHom [Level Λ] [Level Λ'] [srcBound : LevelBound Λ] [trgBound : LevelBound Λ']
  (μ : Λ → Λ') : Prop where
  mono : ∀x ∈ srcBound.valid, ∀y ∈ srcBound.valid, x ≤ y → μ x ≤ μ y
  map_valid : ∀x ∈ srcBound.valid, μ x ∈ trgBound.valid
  map_zero : μ 0 = 0
  map_succ : ∀x ∈ srcBound.valid, μ (SuccOrder.succ x) = SuccOrder.succ (μ x)

instance LevelHom.id [Level Λ] [LevelBound Λ] : LevelHom (Λ := Λ) id where
  mono _ _ _ _ hxy := hxy
  map_valid _ hx := hx
  map_zero := rfl
  map_succ _ _ := rfl

instance LevelHom.comp
  [Level Λ] [Level Λ'] [Level Λ'']
  [srcBound : LevelBound Λ] [midBound : LevelBound Λ'] [trgBound : LevelBound Λ'']
  (μ : Λ → Λ') (ν : Λ' → Λ'') [left : LevelHom μ] [right : LevelHom ν]
  : LevelHom (ν ∘ μ) where
  mono x hx y hy hxy :=
    right.mono (μ x) (left.map_valid x hx) (μ y) (left.map_valid y hy) <| left.mono x hx y hy hxy
  map_valid x hx := right.map_valid (μ x) (left.map_valid x hx)
  map_zero := by simp [left.map_zero, right.map_zero]
  map_succ x hx := by simp [left.map_succ x hx, right.map_succ (μ x) (left.map_valid x hx)]
