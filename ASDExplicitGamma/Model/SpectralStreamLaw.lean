module

public import ASDExplicitGamma.Model.SpectralModel

@[expose] public section

open MeasureTheory Homogenization ProbabilityTheory

namespace ASDExplicitGamma.Model

/-- The finite covariance quadratic form prescribed by the frozen q3 law. -/
noncomputable def q3CovarianceQuadratic {n : ℕ} (h : ℝ) (x : Fin n → Vec 2) (t : Fin n → ℝ) : ℝ :=
  h ^ 2 * ∑ i, ∑ j, t i * t j * q3Cov ((x i - x j) 0) * q3Cov ((x i - x j) 1)

private theorem gaussian_zero_integral_sq (v : NNReal) :
    (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  have hv := variance_eq_integral (μ := gaussianReal 0 v) (X := fun y : ℝ => y)
    measurable_id.aemeasurable
  rw [hv, integral_id_gaussianReal] at h
  simpa only [sub_zero] using h

/-- The Gaussian law computes the squared norm of every finite real stream sum.
The `max` is the exact coercion of `Real.toNNReal`, before covariance positivity
is used. -/
theorem q3StreamSum_norm_sq_max
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    {n : ℕ} (x : Fin n → Vec 2) (t : Fin n → ℝ) :
    ‖∑ i, t i • q3StreamKoopman M (x i) (q3StreamOriginL2 M)‖ ^ 2 =
      max (q3CovarianceQuadratic h x t) 0 := by
  let S := ∑ i, t i • q3StreamKoopman M (x i) (q3StreamOriginL2 M)
  have hS : (S : RegCoeffField 2 → ℝ) =ᵐ[planarRegLaw M]
      fun a => ∑ i, t i * a (x i) 1 0 := by
    have hs := Lp.coeFn_finsetSum Finset.univ
      (fun i => t i • q3StreamKoopman M (x i) (q3StreamOriginL2 M))
    have hsm := ae_all_iff.mpr (fun i : Fin n =>
      Lp.coeFn_smul (t i) (q3StreamKoopman M (x i) (q3StreamOriginL2 M)))
    have he := ae_all_iff.mpr (fun i : Fin n => q3StreamKoopman_apply M (x i))
    filter_upwards [hs, hsm, he] with a hs hsm he
    rw [hs]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsm i]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [he i]
  have hnorm : ‖S‖ ^ 2 = ∫ a : RegCoeffField 2,
      (∑ i, t i * a (x i) 1 0) ^ 2 ∂planarRegLaw M := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hS] with a ha
    rw [ha, Real.inner_apply, pow_two]
  rw [show (∑ i, t i • q3StreamKoopman M (x i) (q3StreamOriginL2 M)) = S from rfl,
    hnorm]
  have hmeas : Measurable (fun a : RegCoeffField 2 => ∑ i, t i * a (x i) 1 0) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (Homogenization.measurable_apply_entry (x i) 1 0)
  have hreg : planarRegLaw M =
      Measure.map Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_toMeasure_eq_map_forgetShell M.P
  calc
    (∫ a : RegCoeffField 2, (∑ i, t i * a (x i) 1 0) ^ 2 ∂planarRegLaw M) =
        ∫ j : Algsuperdiff.Frozen.Assumptions.ShellField 2,
          (∑ i, t i * j (x i) 1 0) ^ 2
            ∂(Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure := by
      rw [hreg, integral_map
        Algsuperdiff.Frozen.Assumptions.ShellField.measurable_forgetShell.aemeasurable
        (hmeas.pow_const 2).aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with j
      simp only [Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
    _ = ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 (Real.toNNReal (q3CovarianceQuadratic h x t)) := by
      simp only [q3CovarianceQuadratic]
      rw [← hM.2 n x t]
      have hms : Measurable (fun j : Algsuperdiff.Frozen.Assumptions.ShellField 2 =>
          ∑ i, t i * j (x i) 1 0) := by
        convert hmeas.comp Algsuperdiff.Frozen.Assumptions.ShellField.measurable_forgetShell using 1
        funext j
        simp only [Function.comp_apply, Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
      exact (integral_map hms.aemeasurable
        (show AEStronglyMeasurable (fun z : ℝ => z ^ 2) _ from by fun_prop)).symm
    _ = max (q3CovarianceQuadratic h x t) 0 := by
      rw [gaussian_zero_integral_sq, Real.coe_toNNReal']

end ASDExplicitGamma.Model
