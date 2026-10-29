module

public import ASDExplicitGamma.Scalar.ChaosEnvelope

/-! The source envelope second/first moment comparison, with the sharp
Hilbert second-chaos moment estimate supplied rather than assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

/-- Every actual finite Gaussian Hilbert envelope has the source L2/L1 moment ratio. -/
theorem finite_gaussian_envelope_second_moment {d n : ℕ} (m : Fin d → ℝ)
    (A : Fin d → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian) :
    Integrable (fun x => (finiteGaussianEnvelope m A x)^2) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, (finiteGaussianEnvelope m A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        (1+Real.sqrt 15)^2*(∫ x, finiteGaussianEnvelope m A x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2 := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let C : ℝ := 1+Real.sqrt 15
  let D : ℝ := 1+(Real.sqrt 15)⁻¹
  let a : ℝ := ∑ i, (m i)^2
  let B := finiteGaussianChaosNormSq A
  let Y := finiteGaussianEnvelope m A
  have hB : Integrable B μ := integrable_finite_gaussian_chaos_norm_sq A hA
  have hB2 : Integrable (fun x => (B x)^2) μ := integrable_finite_gaussian_chaos_norm_fourth A hA
  have hU2 : Integrable (fun x => (C*a+D*B x)^2) μ :=
    integrable_square_const_add_mul μ (C*a) D B hB hB2
  have hYc : Continuous Y := by
    change Continuous (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, (m i+centeredGaussianQuadratic (A i) x)^2)
    unfold centeredGaussianQuadratic
    fun_prop
  have hn (x) : 0 ≤ Y x := finite_gaussian_envelope_nonneg m A x
  have hyb (x) : Y x ≤ C*a+D*B x := finite_gaussian_envelope_majorant m A x
  have hs (x) : (Y x)^2 ≤ (C*a+D*B x)^2 := pow_le_pow_left₀ (hn x) (hyb x) 2
  have hY2 : Integrable (fun x => (Y x)^2) μ := by
    apply hU2.mono' (hYc.pow 2).measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hs x)
  have ha : 0 ≤ a := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hb : 0 ≤ ∫ x, B x ∂μ := integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hvar : (∫ x, (B x)^2 ∂μ) ≤ 15*(∫ x, B x ∂μ)^2 := finite_gaussian_chaos_norm_fourth A hA
  have hmean : (∫ x, Y x ∂μ) = a+(∫ x, B x ∂μ) := (finite_gaussian_envelope_mean m A hA).2
  refine ⟨hY2,?_⟩
  change (∫ x, (Y x)^2 ∂μ) ≤ C^2*(∫ x, Y x ∂μ)^2
  rw [hmean]
  calc
    _ ≤ ∫ x, (C*a+D*B x)^2 ∂μ := integral_mono_ae hY2 hU2 (Filter.Eventually.of_forall hs)
    _ = (C*a)^2+2*(C*a)*D*(∫ x, B x ∂μ)+D^2*(∫ x, (B x)^2 ∂μ) :=
      integral_square_const_add_mul μ (C*a) D B hB hB2
    _ ≤ C^2*(a+(∫ x, B x ∂μ))^2 := by
      have h := chaos_shift_moment_algebra C D a (∫ x, B x ∂μ) (∫ x, (B x)^2 ∂μ)
        chaos_envelope_constants.1.le chaos_envelope_constants.2.2.1 ha hb hvar
        chaos_envelope_constants.2.2.2
      convert h using 1
      ring

end ASDExplicitGamma.Scalar
