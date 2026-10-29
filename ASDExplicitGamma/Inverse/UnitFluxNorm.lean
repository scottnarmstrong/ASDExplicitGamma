module

public import ASDExplicitGamma.Inverse.ClippedMatrixSymmetricNorm
public import Homogenization.Ambient.BlockMatrix

/-! Uniform unit-load comparisons give the genuine Euclidean operator norm. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open scoped ENNReal
noncomputable section

/-- It suffices to bound the complete unit loading population. Homogeneity
is proved internally, without a direction-dependent exceptional event. -/
theorem symmetric_norm_le_of_unit_quadratic (A : Mat 2) (hA : A.IsHermitian) (B : ℝ)
    (hB : 0 ≤ B) (hpos : ∀ v : Vec 2, 0 ≤ dotProduct v (A.mulVec v))
    (hcap : ∀ v : Vec 2, dotProduct v v=1 → dotProduct v (A.mulVec v) ≤ B) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ ≤ B := by
  apply clipped_symmetric_norm_le_of_quadratic A hA B hB hpos
  intro v
  by_cases hv : v=0
  · subst v
    simp
  · let c := ‖WithLp.toLp 2 v‖
    have hc : 0 < c := norm_pos_iff.mpr (by
      intro hh
      exact hv (WithLp.toLp_injective 2 (by simpa only [WithLp.toLp_zero] using hh)))
    have hc2 : c^2=dotProduct v v := clipped_euclidean_norm_sq v
    let u := c⁻¹ • v
    have hu : dotProduct u u=1 := by
      simp only [u,smul_dotProduct,dotProduct_smul,smul_eq_mul]
      rw [← hc2]
      field_simp
    have hqu : dotProduct u (A.mulVec u)=c⁻¹*c⁻¹*dotProduct v (A.mulVec v) := by
      simp only [u,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
      ring
    have hh := mul_le_mul_of_nonneg_left (hcap u hu) (sq_nonneg c)
    rw [hqu] at hh
    have he : c^2*(c⁻¹*c⁻¹*dotProduct v (A.mulVec v))=dotProduct v (A.mulVec v) := by field_simp
    rw [he] at hh
    exact hh.trans_eq (by rw [hc2]; ring)

/-- Extended nonnegative bounds on all unit loads control the actual norm,
including the infinite-majorant case before AE finiteness is supplied. -/
theorem symmetric_norm_of_unit_extended_bound (A : Mat 2) (hA : A.IsHermitian)
    (hpos : ∀ v : Vec 2, 0 ≤ dotProduct v (A.mulVec v)) (B : ℝ≥0∞)
    (hcap : ∀ v : Vec 2, dotProduct v v=1 → ENNReal.ofReal (dotProduct v (A.mulVec v)) ≤ B) :
    ENNReal.ofReal ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ ≤ B := by
  by_cases hB : B=⊤
  · rw [hB]
    exact le_top
  · rw [← ENNReal.ofReal_toReal hB]
    apply ENNReal.ofReal_le_ofReal
    apply symmetric_norm_le_of_unit_quadratic A hA B.toReal ENNReal.toReal_nonneg hpos
    intro v hv
    have hh := ENNReal.toReal_mono hB (hcap v hv)
    rwa [ENNReal.toReal_ofReal (hpos v)] at hh

end
end ASDExplicitGamma.Inverse
