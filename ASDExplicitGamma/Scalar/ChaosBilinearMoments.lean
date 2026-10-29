module

public import ASDExplicitGamma.Scalar.ChaosBilinearCutoff

/-! Actual finite-cutoff moments under the countable Gaussian input law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

/-- Pull back an integrable finite-dimensional observable to the exact countable realization. -/
theorem integrable_gaussian_first_coordinates_comp (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (hi : Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    Integrable (f ∘ gaussianFirstCoordinates n) Gaussian.standardGaussianInfinitePi := by
  have h : Integrable f (Gaussian.standardGaussianInfinitePi.map (gaussianFirstCoordinates n)) := by
    rwa [map_gaussian_first_coordinates]
  exact (integrable_map_measure hf.aestronglyMeasurable (gaussian_first_coordinates_measurable n).aemeasurable).mp h

/-- The finite-coordinate pushforward preserves the actual expectation. -/
theorem integral_gaussian_first_coordinates_comp (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) :
    (∫ omega,f (gaussianFirstCoordinates n omega) ∂Gaussian.standardGaussianInfinitePi)=
      ∫ x,f x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [← map_gaussian_first_coordinates n]
  exact (integral_map (gaussian_first_coordinates_measurable n).aemeasurable hf.aestronglyMeasurable).symm

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The finite Hilbert polynomial envelope is continuous. -/
theorem continuous_finite_hilbert_gaussian_envelope {n : ℕ} (m : W) (B : Fin n → Fin n → W) :
    Continuous (finiteHilbertGaussianEnvelope m B) := by
  unfold finiteHilbertGaussianEnvelope finiteHilbertGaussianQuadratic
  fun_prop

/-- Each true cutoff envelope has integrable first and second moments and the sharp source ratio. -/
theorem gaussian_bilinear_partial_moment_bound (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (n : ℕ) :
    let Y := fun omega => ‖m+gaussianBilinearPartial B v n omega‖^2
    Integrable Y Gaussian.standardGaussianInfinitePi ∧
    Integrable (fun omega => (Y omega)^2) Gaussian.standardGaussianInfinitePi ∧
    (∫ omega,(Y omega)^2 ∂Gaussian.standardGaussianInfinitePi)≤
      (1+Real.sqrt 15)^2*(∫ omega,Y omega ∂Gaussian.standardGaussianInfinitePi)^2 := by
  let f := finiteHilbertGaussianEnvelope m (fun i j : Fin n => B (v i) (v j))
  have hc : Continuous f := continuous_finite_hilbert_gaussian_envelope _ _
  have he := gaussian_bilinear_partial_envelope_eq m B v n
  have h1 := integrable_finite_hilbert_gaussian_envelope_general m (fun i j : Fin n => B (v i) (v j))
  have h2 := finite_hilbert_gaussian_envelope_second_moment_general m (fun i j : Fin n => B (v i) (v j))
  change Integrable _ _ ∧ Integrable _ _ ∧ _
  rw [he]
  refine ⟨integrable_gaussian_first_coordinates_comp n f hc.measurable h1,
    integrable_gaussian_first_coordinates_comp n (fun x => (f x)^2) (hc.pow 2).measurable h2.1,?_⟩
  change (∫ omega,(f (gaussianFirstCoordinates n omega))^2 ∂Gaussian.standardGaussianInfinitePi)≤
    (1+Real.sqrt 15)^2*(∫ omega,f (gaussianFirstCoordinates n omega) ∂Gaussian.standardGaussianInfinitePi)^2
  rw [integral_gaussian_first_coordinates_comp n (fun x => (f x)^2) (hc.pow 2).measurable,
    integral_gaussian_first_coordinates_comp n f hc.measurable]
  exact h2.2

end ASDExplicitGamma.Scalar
