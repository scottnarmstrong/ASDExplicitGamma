module

public import ASDExplicitGamma.Scalar.ChaosHilbertMoment

/-! Symmetrization is an identity for quadratic polynomials; it is not a source hypothesis. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : ℕ}

/-- The actual symmetric coefficient of the same quadratic polynomial. -/
noncomputable def hilbertQuadraticSymmetrization (B : Fin n → Fin n → W) (i j : Fin n) : W :=
  (1/2:ℝ) • (B i j+B j i)

/-- Symmetry is discharged by the definition. -/
theorem hilbert_quadratic_symmetrization_symmetric (B : Fin n → Fin n → W) (i j : Fin n) :
    hilbertQuadraticSymmetrization B i j=hilbertQuadraticSymmetrization B j i := by
  unfold hilbertQuadraticSymmetrization
  rw [add_comm]

/-- Transposing the Hilbert coefficients leaves the quadratic polynomial unchanged. -/
theorem finite_hilbert_gaussian_quadratic_transpose (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) :
    finiteHilbertGaussianQuadratic (fun i j => B j i) x=finiteHilbertGaussianQuadratic B x := by
  unfold finiteHilbertGaussianQuadratic
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp only [mul_comm,eq_comm]

/-- The quadratic envelope is exactly its symmetric representation. -/
theorem finite_hilbert_gaussian_quadratic_symmetrize (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) :
    finiteHilbertGaussianQuadratic (hilbertQuadraticSymmetrization B) x=finiteHilbertGaussianQuadratic B x := by
  calc
    _ = (1/2:ℝ) • finiteHilbertGaussianQuadratic B x+
        (1/2:ℝ) • finiteHilbertGaussianQuadratic (fun i j => B j i) x := by
      simp only [finiteHilbertGaussianQuadratic,hilbertQuadraticSymmetrization,smul_add,
        Finset.sum_add_distrib,Finset.smul_sum,smul_smul,mul_comm]
    _ = _ := by
      rw [finite_hilbert_gaussian_quadratic_transpose,← add_smul]
      norm_num

/-- The same identity at the level of the complete envelope function. -/
theorem finite_hilbert_gaussian_envelope_symmetrize (m : W) (B : Fin n → Fin n → W) :
    finiteHilbertGaussianEnvelope m (hilbertQuadraticSymmetrization B)=finiteHilbertGaussianEnvelope m B := by
  funext x
  unfold finiteHilbertGaussianEnvelope
  rw [finite_hilbert_gaussian_quadratic_symmetrize]

/-- General Hilbert quadratic envelopes are integrable without a symmetry assumption. -/
theorem integrable_finite_hilbert_gaussian_envelope_general (m : W) (B : Fin n → Fin n → W) :
    Integrable (finiteHilbertGaussianEnvelope m B) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := integrable_finite_hilbert_gaussian_envelope m (hilbertQuadraticSymmetrization B)
    (hilbert_quadratic_symmetrization_symmetric B)
  rwa [finite_hilbert_gaussian_envelope_symmetrize] at h

/-- No symmetry premise is needed for the genuine Hilbert-envelope moment comparison. -/
theorem finite_hilbert_gaussian_envelope_second_moment_general (m : W) (B : Fin n → Fin n → W) :
    Integrable (fun x => (finiteHilbertGaussianEnvelope m B x)^2) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x,(finiteHilbertGaussianEnvelope m B x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))≤
      (1+Real.sqrt 15)^2*(∫ x,finiteHilbertGaussianEnvelope m B x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2 := by
  have h := finite_hilbert_gaussian_envelope_second_moment m (hilbertQuadraticSymmetrization B)
    (hilbert_quadratic_symmetrization_symmetric B)
  rwa [finite_hilbert_gaussian_envelope_symmetrize] at h

end ASDExplicitGamma.Scalar
