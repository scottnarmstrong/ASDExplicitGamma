module

public import ASDExplicitGamma.Gaussian.SupMeanGaussianRealizations
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Base-point tensor moments and exact scalar Gaussian concentration parameters. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Centered Gaussian observations have zero actual mean. -/
theorem supMean_gaussian_integral_zero {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) (i : I) :
    (∫ ω, X i ω ∂μ) = 0 := by
  obtain ⟨v,hv⟩ := hX.map_single i
  exact integral_of_map_gaussianReal (hX.1 i) hv

/-- Actual variance is the covariance diagonal, with no replacement covariance premise. -/
theorem supMean_gaussian_variance {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : I → Ω → ℝ}
    (hX : IsCenteredGaussianFamily μ X) (i : I) :
    Var[X i; μ] = ∫ ω, (X i ω)^2 ∂μ := by
  rw [variance_eq_sub (hX.memLp i 2 (by simp)), supMean_gaussian_integral_zero hX i]
  simp only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), sub_zero]

/-- A finite projection has exactly the actual covariance quadratic variance. -/
theorem supMean_gaussian_combination_variance {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : I → Ω → ℝ}
    (hX : IsCenteredGaussianFamily μ X) {ι : Type} [Fintype ι]
    (o : ι → I) (t : ι → ℝ) :
    Var[(fun ω => ∑ i, t i*X (o i) ω); μ] =
      ∑ i, ∑ j, t i*t j*(∫ ω, X (o i) ω*X (o j) ω ∂μ) := by
  let Y : Unit → Ω → ℝ := fun _ ω => ∑ i, t i*X (o i) ω
  have hY : IsCenteredGaussianFamily μ Y :=
    hX.finite_linear_image (fun _ : Unit => o) (fun _ : Unit => t)
  have hh := supMean_gaussian_variance hY ()
  change Var[(fun ω => ∑ i, t i*X (o i) ω); μ] = _ at hh
  rw [hh]
  have hi (i j : ι) : Integrable (fun ω => (t i*t j)*(X (o i) ω*X (o j) ω)) μ :=
    ((hX.memLp (o i) 2 (by simp)).integrable_mul (hX.memLp (o j) 2 (by simp))).const_mul _
  have heq : (fun ω => (∑ i, t i*X (o i) ω)^2) =
      (fun ω => ∑ i, ∑ j, (t i*t j)*(X (o i) ω*X (o j) ω)) := by
    funext ω
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∫ ω, (∑ i, t i*X (o i) ω)^2 ∂μ) = _
  rw [heq, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  simp only [integral_const_mul]

/-- The finite tensor norm is integrable and has exactly the trace second moment. -/
theorem supMean_gaussian_tensor_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) :
    MemLp (fun ω => ‖(WithLp.toLp 2 (fun i => X i ω) : EuclideanSpace ℝ ι)‖) 2 μ ∧
    (∫ ω, ‖(WithLp.toLp 2 (fun i => X i ω) : EuclideanSpace ℝ ι)‖^2 ∂μ) =
      ∑ i, ∫ ω, (X i ω)^2 ∂μ := by
  have hm : MemLp (fun ω => (WithLp.toLp 2 (fun i => X i ω) : EuclideanSpace ℝ ι)) 2 μ :=
    memLp_piLp_iff.mpr (fun i => hX.memLp i 2 (by simp))
  refine ⟨hm.norm, ?_⟩
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact integral_finsetSum Finset.univ (fun i _ => by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hX.memLp i 2 (by simp)).integrable_norm_pow (by decide : 2 ≠ 0))

/-- Jensen's base-point payment is the square root of the actual tensor covariance
trace, rather than the sum of component standard deviations. -/
theorem supMean_gaussian_tensor_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ X) :
    (∫ ω, ‖(WithLp.toLp 2 (fun i => X i ω) : EuclideanSpace ℝ ι)‖ ∂μ) ≤
      Real.sqrt (∑ i, ∫ ω, (X i ω)^2 ∂μ) := by
  obtain ⟨hm, he⟩ := supMean_gaussian_tensor_moment μ X hX
  have hv := variance_nonneg (fun ω => ‖(WithLp.toLp 2 (fun i => X i ω) :
    EuclideanSpace ℝ ι)‖) μ
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply] at hv
  rw [he] at hv
  exact Real.le_sqrt_of_sq_le (by linarith only [hv])

end
end ASDExplicitGamma.Gaussian
