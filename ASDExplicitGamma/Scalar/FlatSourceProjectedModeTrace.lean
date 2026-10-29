module

public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation
public import ASDExplicitGamma.Scalar.Lambda8CovarianceAdapter
public import ASDExplicitGamma.Scalar.DirichletSquareHessian
public import ASDExplicitGamma.Gaussian.BilinearCovariance

/-! The actual q3 local projection has a summable white-noise mode trace. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory
open ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology RealInnerProductSpace

/-- The total squared mode norm of the actual local Dirichlet projection is
bounded by its physical half-variance energy. The mode family is the actual
q3 H³ realization, and the bound is transferred from the source shell law. -/
theorem lambda8Q3ProjectedLoad_modes_energy_le
    {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U)
    (hvol : (volume U).toReal ≠ 0)
    {a b c d : ℝ} (hUK : U ⊆ openRectangle a b c d)
    (hab : a < b) (hcd : c < d) (e : Vec 2)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    (∑' n : ℕ, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
      (q3H3RangeValue a b c d
        (q3ModelAmplitude M h k) (q3ModelLength k)
        (q3H3Directions a b c d (q3ModelAmplitude M h k)
          (q3ModelLength k) whiteBasis n))‖ ^ 2) ≤
      (volume U).toReal *
        ((h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2) := by
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let dirs := q3H3Directions a b c d β L whiteBasis
  let hs := q3H3Directions_summable a b c d β L whiteBasis
  let Z := @gaussianSeriesLimitE
    (Q3H3Range a b c d β L) (HilbertVectorL2 U)
    inferInstance (instQ3H3RangeInnerProductSpace a b c d β L)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance dirs hs
    ((lambda8Q3ProjectedLoadClass hU a b c d hab hcd e).comp
      (q3H3RangeValue a b c d β L))
  let R : Q3H3Range a b c d β L →L[ℝ] HilbertVectorL2 U :=
    (lambda8Q3ProjectedLoadClass hU a b c d hab hcd e).comp
      (q3H3RangeValue a b c d β L)
  have htrace := @integral_bilinear_diagonal
    (Q3H3Range a b c d β L) (HilbertVectorL2 U)
    inferInstance (instQ3H3RangeInnerProductSpace a b c d β L)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    dirs hs R (innerSL ℝ)
  have htrace' :
      (∫ ω, ‖Z ω‖ ^ 2
        ∂standardGaussianInfinitePi) =
        ∑' n : ℕ, ‖R (dirs n)‖ ^ 2 := by
    calc
      _ = ∫ ω, innerSL ℝ (Z ω) (Z ω) ∂standardGaussianInfinitePi := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
      _ = ∑' n : ℕ, innerSL ℝ (R (dirs n)) (R (dirs n)) := htrace
      _ = _ := by
        apply tsum_congr
        intro n
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  have hactual := lambda8Q3ProjectedLoad_actualShellLaw
    hU a b c d hab hcd e M h hM k
  have hbound := lambda8Q3ProjectedLoadClass_volumeNormalized_energy_le
    hU hvol hUK hab hcd e M h hM he k
  have hvolnn : 0 ≤ (volume U).toReal := ENNReal.toReal_nonneg
  have hZ : ∀ ω, Z ω = R (q3H3Series a b c d β L whiteBasis ω) := by
    intro ω
    rfl
  calc
    _ = ∫ ω, ‖Z ω‖ ^ 2 ∂standardGaussianInfinitePi := htrace'.symm
    _ = ∫ ω, ‖R (q3H3Series a b c d β L whiteBasis ω)‖ ^ 2
        ∂standardGaussianInfinitePi := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [hZ ω]
    _ = ∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
        (q3C1Series a b c d β L whiteBasis ω 0)‖ ^ 2
        ∂standardGaussianInfinitePi := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rfl
    _ = ∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
        (Gaussian.shellFieldScalarRestriction (closedRectangle a b c d)
          (ω.1 k))‖ ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure := hactual.symm
    _ ≤ (volume U).toReal *
        ((h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2) := by
      have hmul := mul_le_mul_of_nonneg_left hbound hvolnn
      calc
        _ = (volume U).toReal *
            ((volume U).toReal⁻¹ *
              ∫ ω, ‖lambda8Q3ProjectedLoadClass hU a b c d hab hcd e
                (Gaussian.shellFieldScalarRestriction (closedRectangle a b c d)
                  (ω.1 k))‖ ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
          rw [← mul_assoc, mul_inv_cancel₀ hvol, one_mul]
        _ ≤ _ := hmul

/-- The exact Gaussian mode trace of the local projection's weak gradient is
the directional q3 derivative variance. This is the gradient-energy input
for the flat physical source. -/
theorem lambda8Q3GaussianModeParent_hessian_energy_trace
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2) :
    (∑' n : Gaussian.whiteBasisIndex,
      (lambda8Q3GaussianModeParentHessian Q β L v n).frobeniusNormalizedL2 Q ^ 2) =
      β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := by
  have htrace := lambda8Q3GaussianModeDerivative_energy_tsum Q β L v
  have hmode (n : Gaussian.whiteBasisIndex) :
      (lambda8Q3GaussianModeParentHessian Q β L v n).frobeniusNormalizedL2 Q ^ 2 =
        energy Q (lambda8Q3GaussianModeDerivative β L v n) := by
    let u := lambda8Q3GaussianModeParentPotential Q β L v n
    let H := lambda8Q3GaussianModeParentHessian Q β L v n
    have hdiv := (lambda8Q3GaussianModeParentPotential_spec Q β L v n).2
    have hmemLap : MemLp (dirichletWeakLaplacian H) 2 (normalizedCubeMeasure Q) :=
      memLp_dirichlet_weak_laplacian H
    have hmemDeriv :
        MemLp (lambda8Q3GaussianModeDerivative β L v n) 2
          (normalizedCubeMeasure Q) :=
      (memLp_congr_ae hdiv).mp hmemLap
    have hnorm : cubeLpNorm Q 2 (dirichletWeakLaplacian H) =
        cubeLpNorm Q 2 (lambda8Q3GaussianModeDerivative β L v n) := by
      unfold cubeLpNorm
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hdiv)
    calc
      _ = cubeLpNorm Q 2 (dirichletWeakLaplacian H) ^ 2 := by
        rw [dirichlet_square_hessian_identity Q u H]
      _ = cubeLpNorm Q 2 (lambda8Q3GaussianModeDerivative β L v n) ^ 2 := by
        rw [hnorm]
      _ = energy Q (lambda8Q3GaussianModeDerivative β L v n) :=
        (energy_eq_cubeLpNorm_sq Q hmemDeriv).symm
  calc
    _ = ∑' n : Gaussian.whiteBasisIndex,
        energy Q (lambda8Q3GaussianModeDerivative β L v n) :=
      tsum_congr hmode
    _ = β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) * (v 0 ^ 2 + v 1 ^ 2) := htrace.2

end ASDExplicitGamma.Scalar
