module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetGaussianClosure

/-! Genuine strong L2 convergence from centered Gaussian remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter ASDExplicitGamma.Gaussian
open scoped Topology
noncomputable section

/-- Almost-sure convergence of centered Gaussian L2 remainders to zero
implies strong L2 convergence, because their actual variances converge to zero.
No domination or fourth-moment bound is assumed. -/
theorem upper_cell_reset_gaussian_L2_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Lp ℝ 2 μ)
    (hF : ∀ n,∃ v : NNReal,μ.map (F n)=gaussianReal 0 v)
    (hl : ∀ᵐ ω ∂μ,Tendsto (fun n => F n ω) atTop (𝓝 (0:ℝ))) :
    Tendsto F atTop (𝓝 0) := by
  choose v hv using hF
  have hi := tendsto_integral_sq_gaussian_of_ae_limit μ (fun n ω => F n ω) (fun _ => 0) v
    (fun n => (Lp.memLp (F n)).aestronglyMeasurable.aemeasurable)
    aemeasurable_const hv hl
  simp only [zero_pow (by norm_num : 2≠0),integral_zero] at hi
  have hn (n : ℕ) : ‖F n‖^2=∫ ω,(F n ω)^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hs : Tendsto (fun n => ‖F n‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [hn] using hi
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have ht : Tendsto (fun n => ‖F n‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hroot
  exact tendsto_zero_iff_norm_tendsto_zero.mpr ht

end
end ASDExplicitGamma.Scalar
