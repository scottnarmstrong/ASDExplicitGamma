module

public import ASDExplicitGamma.Gaussian.FiniteProjectionLaw
public import ASDExplicitGamma.Scalar.ChaosHilbertMoment
public import ASDExplicitGamma.Numerics.Scalar.Readable

/-! Finite Hilbert-valued quadratic chaos bounds on the actual infinite Gaussian
coordinate realization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ASDExplicitGamma.Scalar

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {N : ℕ}

/-- The finite-dimensional Hilbert-envelope bound, pulled back to the first
`N` coordinates of the campaign's actual infinite standard Gaussian law. -/
theorem finite_hilbert_gaussian_envelope_128_bound_infinite
    (m : W) (B : Fin N → Fin N → W) (hB : ∀ i j, B i j = B j i) :
    eLpNorm
        (fun ω : ℕ → ℝ => finiteHilbertGaussianEnvelope m B
          (WithLp.toLp 2 (fun i : Fin N => ω i.val)))
        (ENNReal.ofReal (128 / 127 : ℝ)) Gaussian.standardGaussianInfinitePi ≤
      ENNReal.ofReal ((513 / 500 : ℝ) *
        (∫ x, finiteHilbertGaussianEnvelope m B x
          ∂stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
  let E := EuclideanSpace ℝ (Fin N)
  let F : EuclideanSpace ℝ (Fin N) → ℝ := finiteHilbertGaussianEnvelope m B
  have hFcont : Continuous F := by
    change Continuous (fun x : EuclideanSpace ℝ (Fin N) =>
      ‖m + finiteHilbertGaussianQuadratic B x‖ ^ 2)
    unfold finiteHilbertGaussianQuadratic
    fun_prop
  have hF : AEStronglyMeasurable F (stdGaussian E) := hFcont.aestronglyMeasurable
  have hmap : (Gaussian.standardGaussianPi N).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℝ (Fin N)) := by
    simpa [E, Gaussian.standardGaussianPi] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin N))
  let Fpi : (Fin N → ℝ) → ℝ := fun x => F (WithLp.toLp 2 x)
  have hFpi : AEStronglyMeasurable Fpi (Gaussian.standardGaussianPi N) := by
    exact (hFcont.comp (by fun_prop)).aestronglyMeasurable
  have hfinite :
      eLpNorm F (ENNReal.ofReal (128 / 127 : ℝ)) (stdGaussian E) =
        eLpNorm Fpi (ENNReal.ofReal (128 / 127 : ℝ)) (Gaussian.standardGaussianPi N) := by
    have hFmap : AEStronglyMeasurable F
        ((Gaussian.standardGaussianPi N).map (WithLp.toLp 2)) := by
      rw [hmap]
      exact hF
    rw [← hmap]
    exact eLpNorm_map_measure hFmap (by fun_prop)
  have hbound0 := finite_hilbert_gaussian_envelope_conjugate_bound
    m B hB 128 (by norm_num)
  have hbound : eLpNorm F (ENNReal.ofReal (128 / 127 : ℝ)) (stdGaussian E) ≤
      ENNReal.ofReal ((513 / 500 : ℝ) *
        (∫ x, F x ∂stdGaussian E)) := by
    norm_num only [show (2 / (128 : ℝ)) = (1 / 64 : ℝ) by norm_num] at hbound0
    apply hbound0.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right Numerics.Scalar.f7_factors_source.2.1.le
      (integral_nonneg (fun x => sq_nonneg _))
  have hinfinite :
      eLpNorm (fun ω : ℕ → ℝ => Fpi (fun i : Fin N => ω i.val))
          (ENNReal.ofReal (128 / 127 : ℝ)) Gaussian.standardGaussianInfinitePi =
        eLpNorm Fpi (ENNReal.ofReal (128 / 127 : ℝ)) (Gaussian.standardGaussianPi N) :=
    Gaussian.eLpNorm_standardGaussian_firstCoordinates N Fpi hFpi _
  rw [hinfinite]
  exact hfinite ▸ hbound

end ASDExplicitGamma.Scalar
