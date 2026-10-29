module

public import ASDExplicitGamma.Scalar.ChaosHilbert
public import ASDExplicitGamma.Scalar.ChaosAffineMoment

/-! The source nonnegative Gaussian envelope |m+c|², with deterministic m
and genuine vector second-chaos c, in finite orthonormal coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

noncomputable def finiteGaussianEnvelope {d n : ℕ} (m : Fin d → ℝ)
    (A : Fin d → Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, (m i+centeredGaussianQuadratic (A i) x)^2

theorem finite_gaussian_envelope_nonneg {d n : ℕ} (m : Fin d → ℝ)
    (A : Fin d → Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ finiteGaussianEnvelope m A x := Finset.sum_nonneg (fun i _ => sq_nonneg (m i+centeredGaussianQuadratic (A i) x))

/-- The deterministic part is orthogonal in expectation to the centered quadratic part. -/
theorem finite_gaussian_envelope_mean {d n : ℕ} (m : Fin d → ℝ)
    (A : Fin d → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian) :
    Integrable (finiteGaussianEnvelope m A) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, finiteGaussianEnvelope m A x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        (∑ i, (m i)^2)+(∫ x, finiteGaussianChaosNormSq A x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hI (i : Fin d) : Integrable (fun x => centeredGaussianQuadratic (A i) x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa only [pow_one] using integrable_centered_gaussian_quadratic_power (A i) (hA i) 1
  have he (i : Fin d) : (fun x => (m i+centeredGaussianQuadratic (A i) x)^2) =
      fun x => (m i)^2+(2*m i)*centeredGaussianQuadratic (A i) x+(centeredGaussianQuadratic (A i) x)^2 := by
    funext x
    ring
  have hFirst (i : Fin d) : Integrable (fun x => (m i)^2+(2*m i)*centeredGaussianQuadratic (A i) x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    convert (integrable_const ((m i)^2)).add ((hI i).const_mul (2*m i)) using 1
  have hCoord (i : Fin d) : Integrable (fun x => (m i+centeredGaussianQuadratic (A i) x)^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [he i]
    convert ((integrable_const ((m i)^2)).add ((hI i).const_mul (2*m i))).add
      (integrable_centered_gaussian_quadratic_power (A i) (hA i) 2) using 1
  refine ⟨integrable_finsetSum _ (fun i _ => hCoord i),?_⟩
  unfold finiteGaussianEnvelope finiteGaussianChaosNormSq
  rw [integral_finsetSum _ (fun i _ => hCoord i),integral_finsetSum _ (fun i _ =>
    integrable_centered_gaussian_quadratic_power (A i) (hA i) 2),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [he i,integral_add (hFirst i)
    (integrable_centered_gaussian_quadratic_power (A i) (hA i) 2),
    integral_add (integrable_const ((m i)^2)) ((hI i).const_mul (2*m i)),integral_const_mul,
    centered_gaussian_quadratic_mean_zero (A i) (hA i)]
  simp

/-- The exact weighted-square majorant for the source envelope. -/
theorem finite_gaussian_envelope_majorant {d n : ℕ} (m : Fin d → ℝ)
    (A : Fin d → Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianEnvelope m A x ≤
      (1+Real.sqrt 15)*(∑ i, (m i)^2)+(1+(Real.sqrt 15)⁻¹)*finiteGaussianChaosNormSq A x :=
  chaos_weighted_norm_square (Real.sqrt 15) (Real.sqrt_pos.mpr (by norm_num)) m
    (fun i => centeredGaussianQuadratic (A i) x)

end ASDExplicitGamma.Scalar
