module

public import ASDExplicitGamma.Cold.PositiveTraceProduct
public import ASDExplicitGamma.Cold.MatrixFrobeniusAlgebra
public import Mathlib.Tactic.NoncommRing

/-! # The actual two-sided matrix order behind the cold graph sandwich -/

@[expose] public section
noncomputable section
open Matrix
namespace ASDExplicitGamma.Cold

/-- The inverse square completion gives A+A^{-1}>=2I. -/
theorem matrix_add_inverse_sub_two_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) : (A+A⁻¹-2 • (1:Matrix n n ℝ)).PosSemidef := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have h := hA.inv.posSemidef.conjTranspose_mul_mul_same (A-1)
  have he : (A-1)ᴴ*A⁻¹*(A-1) = A+A⁻¹-2 • (1:Matrix n n ℝ) := by
    rw [Matrix.conjTranspose_sub,hA.1.eq,Matrix.conjTranspose_one]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
      Matrix.mul_nonsing_inv A hdet,Matrix.nonsing_inv_mul A hdet,
      two_smul]
    noncomm_ring
  rwa [he] at h

/-- Coarse duality and parent/child order imply the exact lower sandwich. -/
theorem cold_graph_lower_sandwich {n : Type*} [Fintype n] [DecidableEq n]
    {A X R : Matrix n n ℝ} (hA : A.PosDef) (hR : R.IsHermitian)
    (hdual : (R*A*R-A⁻¹).PosSemidef) (hsub : (X-A).PosSemidef) :
    (A+R*X*R-2 • (1:Matrix n n ℝ)).PosSemidef := by
  have hbase := matrix_add_inverse_sub_two_posSemidef hA
  have hdiff := hsub.conjTranspose_mul_mul_same R
  rw [hR.eq] at hdiff
  have h := (hbase.add hdual).add hdiff
  convert h using 1
  noncomm_ring

/-- The trace-product sign gives the pathwise Frobenius sandwich inequality. -/
theorem cold_graph_sandwich_pathwise {n : Type*} [Fintype n] [DecidableEq n]
    {H U V : Matrix n n ℝ} (hH : H.IsHermitian)
    (hupper : (U-H).PosSemidef) (hlower : (H+V).PosSemidef) :
    matrixFrobeniusSq H ≤ matrixFrobeniusInner (U-V) H+(U*V).trace := by
  have h := trace_mul_nonneg_of_posSemidef hupper hlower
  have he : ((U-H)*(H+V)).trace = (U*H).trace-(V*H).trace+(U*V).trace-(H*H).trace := by
    rw [Matrix.sub_mul,Matrix.mul_add,Matrix.mul_add,Matrix.trace_sub,Matrix.trace_add,Matrix.trace_add]
    rw [Matrix.trace_mul_comm H V]
    ring
  rw [he] at h
  have hinner : matrixFrobeniusInner (U-V) H = (U*H).trace-(V*H).trace := by
    rw [matrixFrobeniusInner_eq_trace_mul _ hH,Matrix.sub_mul,Matrix.trace_sub]
  rw [hinner,matrixFrobeniusSq_eq_trace_mul hH]
  linarith only [h]

end ASDExplicitGamma.Cold
