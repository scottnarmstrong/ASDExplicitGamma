module

public import ASDExplicitGamma.Scalar.ChaosHilbertCoordinates

/-! Sharp finite-input Gaussian envelope moments for arbitrary Hilbert outputs. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : ℕ}

/-- The actual Hilbert norm-squared envelope. -/
noncomputable def finiteHilbertGaussianEnvelope (m : W) (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := ‖m+finiteHilbertGaussianQuadratic B x‖^2

/-- The finite coordinate representation is exact as a function, including zero-dimensional spans. -/
theorem finite_hilbert_gaussian_envelope_eq (m : W) (B : Fin n → Fin n → W) :
    finiteHilbertGaussianEnvelope m B=
      finiteGaussianEnvelope (finiteHilbertChaosMean m B) (finiteHilbertChaosMatrix m B) :=
  funext (finite_hilbert_gaussian_envelope_coordinates m B)

/-- Genuine Hilbert-valued envelopes have an integrable expectation. -/
theorem integrable_finite_hilbert_gaussian_envelope (m : W) (B : Fin n → Fin n → W)
    (hB : ∀ i j,B i j=B j i) :
    Integrable (finiteHilbertGaussianEnvelope m B) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [finite_hilbert_gaussian_envelope_eq]
  exact (finite_gaussian_envelope_mean _ _ (finite_hilbert_chaos_matrix_hermitian m B hB)).1

/-- The full Hilbert-output second moment has the source constant, without a moment-bound premise. -/
theorem finite_hilbert_gaussian_envelope_second_moment (m : W) (B : Fin n → Fin n → W)
    (hB : ∀ i j,B i j=B j i) :
    Integrable (fun x => (finiteHilbertGaussianEnvelope m B x)^2) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x,(finiteHilbertGaussianEnvelope m B x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))≤
      (1+Real.sqrt 15)^2*(∫ x,finiteHilbertGaussianEnvelope m B x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2 := by
  rw [finite_hilbert_gaussian_envelope_eq]
  exact finite_gaussian_envelope_second_moment _ _ (finite_hilbert_chaos_matrix_hermitian m B hB)

/-- The corrected source conjugate norm bound for arbitrary Hilbert outputs and finite Gaussian inputs. -/
theorem finite_hilbert_gaussian_envelope_conjugate_bound (m : W) (B : Fin n → Fin n → W)
    (hB : ∀ i j,B i j=B j i) (p : ℝ) (hp : 2≤p) :
    eLpNorm (finiteHilbertGaussianEnvelope m B) (ENNReal.ofReal (p/(p-1)))
      (stdGaussian (EuclideanSpace ℝ (Fin n)))≤
    ENNReal.ofReal ((1+Real.sqrt 15)^(2/p)*
      (∫ x,finiteHilbertGaussianEnvelope m B x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  rw [finite_hilbert_gaussian_envelope_eq]
  exact finite_gaussian_envelope_conjugate_bound _ _ (finite_hilbert_chaos_matrix_hermitian m B hB) p hp

end ASDExplicitGamma.Scalar
