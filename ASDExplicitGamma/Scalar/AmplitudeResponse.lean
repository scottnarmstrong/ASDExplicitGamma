module

public import ASDExplicitGamma.Variational.AdapterMu
public import ASDExplicitGamma.Statements.ShellVarianceSum
public import Homogenization.Book.Ch04.Theorems.BlockResponseConcentration

/-! Paired rescaling of the actual quadratic doubled response. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational Homogenization.Book.Ch04

/-- The dual source load scales by the inverse diagonal congruence. -/
theorem loadRescale_pairing {d : ℕ} (P Q : BlockVec d) (s : ℝ) (hs : s≠0) :
    blockVecDot (loadRescale s P) (loadRescale s⁻¹ Q)=blockVecDot P Q := by
  simp only [loadRescale,inv_inv,blockVecDot,vecDot_smul_left,vecDot_smul_right]
  field_simp

/-- Reflection reverses the coefficient-amplitude congruence. -/
theorem blockReflect_coarseMatrixRescale {d : ℕ} (A : BlockMat d) (s : ℝ) :
    blockReflect (coarseMatrixRescale s A)=coarseMatrixRescale s⁻¹ (blockReflect A) := by
  cases A
  simp only [blockReflect,coarseMatrixRescale,BlockMat.mk.injEq]
  refine ⟨?_,trivial,trivial,?_⟩ <;> ext i j <;>
    simp only [Matrix.smul_apply,smul_eq_mul,zpow_neg,zpow_ofNat,inv_pow,inv_inv]

/-- The literal doubled quadratic response transforms with paired primal and dual loads. -/
theorem blockJQuadratic_amplitude {d : ℕ} (A : BlockMat d) (P Q : BlockVec d)
    (s : ℝ) (hs : s≠0) :
    blockJQuadraticFullBlockMat (toFullBlockMat A) (loadRescale s P) (loadRescale s⁻¹ Q)=
      blockJQuadraticFullBlockMat (toFullBlockMat (coarseMatrixRescale s A)) P Q := by
  simp only [blockJQuadraticFullBlockMat,fullBlockReflect_toFullBlockMat,
    fullBlockQuadraticCh04_toFullBlockMat]
  rw [← blockVecDot_coarseMatrixRescale_eq A P hs,
    ← blockVecDot_coarseMatrixRescale_eq (blockReflect A) Q (inv_ne_zero hs),
    ← blockReflect_coarseMatrixRescale A s,loadRescale_pairing P Q s hs]

end ASDExplicitGamma.Scalar
