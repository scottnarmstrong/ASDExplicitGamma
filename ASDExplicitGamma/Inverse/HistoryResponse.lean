module

public import ASDExplicitGamma.Inverse.ClippedMatrixGoodCap

/-! Pure-flux compression of the true-frame coarse response. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The literal lower-right block quadratic is the doubled pure-flux one. -/
theorem lower_right_quadratic (C : BlockMat 2) (v : Vec 2) :
    dotProduct v (C.lowerRight.mulVec v)=blockVecDot (0,v) (blockMatVecMul C (0,v)) := by
  simp [blockVecDot,blockMatVecMul,vecDot,matVecMul,Matrix.mulVec,dotProduct]

/-- Positive symmetric doubled matrices control the Euclidean operator norm
of their pure-flux compression with constant one. -/
theorem positive_lower_right_norm_le (C : BlockMat 2) (hC : IsSymmetricBlockMat C)
    (hpos : ∀ P : BlockVec 2, 0 ≤ blockVecDot P (blockMatVecMul C P)) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C.lowerRight‖ ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat C)‖ := by
  have hHerm : C.lowerRight.IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact hC (Sum.inr j) (Sum.inr i)
  apply clipped_symmetric_norm_le_of_quadratic _ hHerm _ (norm_nonneg _)
  · intro v
    rw [lower_right_quadratic]
    exact hpos (0,v)
  · intro v
    have hh := clipped_quadratic_abs_le_norm (toFullBlockMat C) (toFullBlockVec (0,v))
    have he := fullMatrixQuadratic_block C (0,v)
    change dotProduct (toFullBlockVec (0,v)) ((toFullBlockMat C).mulVec (toFullBlockVec (0,v)))=_ at he
    rw [he] at hh
    have hv : dotProduct (toFullBlockVec (0,v)) (toFullBlockVec (0,v))=dotProduct v v := by
      simp only [dotProduct,toFullBlockVec,Fintype.sum_sum_type,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add]
    rw [hv] at hh
    rw [lower_right_quadratic]
    exact (le_abs_self _).trans hh

/-- The source response envelope lies below its safe linear cap. -/
theorem response_envelope_le_linear (t : ℝ) (ht : 0 ≤ t) :
    1+t+Real.sqrt (t*(t+2)) ≤ 2*(1+t) := by
  have hs : Real.sqrt (t*(t+2)) ≤ 1+t := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith only [ht],by nlinarith only [ht]⟩
  linarith only [hs]

end
end ASDExplicitGamma.Inverse
