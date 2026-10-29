module

public import ASDExplicitGamma.Scalar.ViscosityAlgebra
public import ASDExplicitGamma.Variational.AdapterMu

/-! Pointwise viscosity comparison for the actual doubled coefficient with fixed skew part. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization

/-- The source integrand is exactly nu P+Q/nu, before the common factor one half. -/
theorem molecular_doubled_quadratic {d : ℕ} (A : Mat d) (nu : ℝ) (hnu : nu ≠ 0)
    (hs : symmPart A=nu • (1:Mat d)) (p q : Vec d) :
    blockVecDot (p,q) (blockMatVecMul (blockMatrixOfCoeff A) (p,q)) =
      nu*vecDot p p+vecDot (q-matVecMul (skewPart A) p) (q-matVecMul (skewPart A) p)/nu := by
  rw [blockMatrixOfCoeff_quadratic_eq,hs,nonsing_inv_smul nu hnu (by simp),inv_one]
  have hid (v : Vec d) : matVecMul (1 : Mat d) v=v := Matrix.one_mulVec v
  rw [smul_matVecMul,smul_matVecMul,hid,hid,vecDot_smul_right,vecDot_smul_right]
  rw [div_eq_mul_inv,mul_comm (nu⁻¹)]

/-- The exact pointwise comparison uses a common skew part, not an amplitude-rescaled field. -/
theorem fixed_skew_block_energy_comparison {d : ℕ} (A B : Mat d) (nu r : ℝ)
    (hnu : 0 < nu) (hr : 0 < r) (hr1 : r ≤ 1)
    (hA : symmPart A=nu • (1:Mat d)) (hB : symmPart B=(r*nu) • (1:Mat d))
    (hk : skewPart A=skewPart B) (p q : Vec d) :
    r*blockVecDot (p,q) (blockMatVecMul (blockMatrixOfCoeff A) (p,q)) ≤
      blockVecDot (p,q) (blockMatVecMul (blockMatrixOfCoeff B) (p,q)) ∧
    blockVecDot (p,q) (blockMatVecMul (blockMatrixOfCoeff B) (p,q)) ≤
      r⁻¹*blockVecDot (p,q) (blockMatVecMul (blockMatrixOfCoeff A) (p,q)) := by
  rw [molecular_doubled_quadratic A nu hnu.ne' hA,
    molecular_doubled_quadratic B (r*nu) (mul_pos hr hnu).ne' hB,← hk]
  exact viscosity_cost_comparison nu r (vecDot p p)
    (vecDot (q-matVecMul (skewPart A) p) (q-matVecMul (skewPart A) p)) hnu hr hr1
    (vecNormSq_nonneg p) (vecNormSq_nonneg _)

end ASDExplicitGamma.Scalar
