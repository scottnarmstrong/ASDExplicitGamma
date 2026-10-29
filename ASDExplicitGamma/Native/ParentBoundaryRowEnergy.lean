module

public import ASDExplicitGamma.Native.ParentBoundaryWhiteOperator
public import ASDExplicitGamma.Native.OldSignedProjectedKernelBounds
public import ASDExplicitGamma.Native.ParentBoundaryRowTesting

/-! Integrated value and sharp derivative operator bounds for the actual
physical q3 white row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- The genuine physical white row acts on every L2 field with squared
operator norm b², without any modewise supremum. -/
theorem parent_boundary_white_row_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (f : Vec 2 → WhiteNoise)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => inner ℝ (q3Section b L h3Zero x) (f x)) ≤ b^2*hilbertEnergy Q f := by
  have hB := main_continuous_memLp_top Q (q3Section_continuous b L h3Zero)
  have hp : MemLp (fun x => inner ℝ (q3Section b L h3Zero x) (f x)) 2
      (normalizedCubeMeasure Q) := (innerSL ℝ).memLp_of_bilin 2 hB hf
  rw [energy_eq_integral_sq,hilbertEnergy,←integral_const_mul]
  apply integral_mono_ae hp.integrable_sq ((hf.integrable_norm_pow (by norm_num)).const_mul _)
  filter_upwards with x
  have hh := (sq_le_sq₀ (abs_nonneg (inner ℝ (q3Section b L h3Zero x) (f x)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (abs_real_inner_le_norm _ _)
  simpa only [sq_abs,mul_pow,old_signed_raw_white_norm_sq] using hh

/-- Every actual derivative-row contraction has genuine L2 membership. -/
theorem parent_boundary_derivative_row_memLp (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (f : Vec 2 → WhiteNoise)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (i : Fin 2) :
    MemLp (fun x => inner ℝ ((fderiv ℝ (q3Section b L h3Zero) x) (basisVec i)) (f x))
      2 (normalizedCubeMeasure Q) :=
  (innerSL ℝ).memLp_of_bilin 2
    (main_continuous_memLp_top Q
      (((old_signed_white_section_contDiff b L).continuous_fderiv (by norm_num)).clm_apply continuous_const)) hf

/-- Summing the actual spatial derivative rows costs sigma²/2, exactly
the covariance OPERATOR bound rather than its doubled Frobenius trace. -/
theorem parent_boundary_derivative_row_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (f : Vec 2 → WhiteNoise)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (∑ i : Fin 2,energy Q (fun x =>
      inner ℝ ((fderiv ℝ (q3Section b L h3Zero) x) (basisVec i)) (f x))) ≤
      (mainFlatSigmaSq b L/2)*hilbertEnergy Q f := by
  simp only [energy_eq_integral_sq]
  rw [←integral_finsetSum Finset.univ (fun i _ =>
      (parent_boundary_derivative_row_memLp Q b L f hf i).integrable_sq),
    hilbertEnergy,←integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum _ (fun i _ =>
    (parent_boundary_derivative_row_memLp Q b L f hf i).integrable_sq))
    ((hf.integrable_norm_pow (by norm_num)).const_mul _)
  exact Filter.Eventually.of_forall (fun x => parent_boundary_white_derivative_operator b L x (f x))

end
end ASDExplicitGamma.Native
