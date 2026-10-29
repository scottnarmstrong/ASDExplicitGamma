module

public import ASDExplicitGamma.Response.ResponseRealization

/-! Pointwise convex duality for the actual planar doubled energy in the fixed physical frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response

/-- The source exchange R swaps potential and flux. -/
def scalarBlockExchange (X : BlockVec 2) : BlockVec 2 := (X.2,X.1)

/-- Completing the square in the actual self-dual doubled coefficient gives Fenchel's inequality. -/
theorem scalar_block_fenchel (ν σ κ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (X Z : BlockVec 2) :
    2*blockVecDot (scalarBlockExchange X) Z-responseFrameEnergyDensity ν σ κ Z ≤
      responseFrameEnergyDensity ν σ κ X := by
  have hid : responseFrameEnergyDensity ν σ κ X+responseFrameEnergyDensity ν σ κ Z-
      2*blockVecDot (scalarBlockExchange X) Z=
      (ν/σ)*vecNormSq (Z.1-(σ/ν) • (X.2-(κ/σ) • matVecMul responsePlanarJ X.1))+
      (σ/ν)*vecNormSq (Z.2-(κ/σ) • matVecMul responsePlanarJ Z.1-(ν/σ) • X.1) := by
    simp [responseFrameEnergyDensity,scalarBlockExchange,blockVecDot,vecNormSq,vecDot,
      matVecMul,responsePlanarJ,Fin.sum_univ_two]
    field_simp [hν.ne',hσ.ne']
    ring
  have hp : 0 ≤ (ν/σ)*vecNormSq (Z.1-(σ/ν) • (X.2-(κ/σ) • matVecMul responsePlanarJ X.1))+
      (σ/ν)*vecNormSq (Z.2-(κ/σ) • matVecMul responsePlanarJ Z.1-(ν/σ) • X.1) :=
    add_nonneg (mul_nonneg (div_nonneg hν.le hσ.le) (vecNormSq_nonneg _))
      (mul_nonneg (div_nonneg hσ.le hν.le) (vecNormSq_nonneg _))
  rw [← hid] at hp
  linarith only [hp]

end ASDExplicitGamma.Scalar
