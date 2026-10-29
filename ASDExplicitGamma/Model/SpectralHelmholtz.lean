module

public import ASDExplicitGamma.Model.SpectralComplexCore
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

open MeasureTheory Complex
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Model

/-- Complex spectral vector fields, with the Hilbert product norm. -/
abbrev Q3SpectralVector (h : ℝ) :=
  WithLp 2 (Lp ℂ 2 (q3SpectralMeasure h) × Lp ℂ 2 (q3SpectralMeasure h))

/-- The normalized spectral gradient on its full weighted domain. -/
noncomputable def q3SpectralGradientMap (h : ℝ) :
    Lp ℂ 2 (q3SpectralGraphMeasure h) →L[ℂ] Q3SpectralVector h :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    ((q3SpectralGraphCoordinate h 0).prod (q3SpectralGraphCoordinate h 1))

theorem q3SpectralGradientMap_fst (h : ℝ) (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) :
    (q3SpectralGradientMap h p).fst = q3SpectralGraphCoordinate h 0 p := rfl

theorem q3SpectralGradientMap_snd (h : ℝ) (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) :
    (q3SpectralGradientMap h p).snd = q3SpectralGraphCoordinate h 1 p := rfl

/-- The closed potential subspace in the spectral vector model. -/
noncomputable def q3SpectralPotentialSubspace (h : ℝ) : Submodule ℂ (Q3SpectralVector h) :=
  (LinearMap.range (q3SpectralGradientMap h).toLinearMap).topologicalClosure

instance q3SpectralPotentialSubspace_hasOrthogonalProjection (h : ℝ) :
    (q3SpectralPotentialSubspace h).HasOrthogonalProjection := by
  have hcomplete : CompleteSpace (q3SpectralPotentialSubspace h) := by
    change CompleteSpace (LinearMap.range (q3SpectralGradientMap h).toLinearMap).topologicalClosure
    infer_instance
  infer_instance

/-- Pairing of a spectral vector with its frequency. -/
noncomputable def q3SpectralRadialPairing (h : ℝ) (F : Q3SpectralVector h)
    (ξ : Q3FrequencyPlane) : ℂ :=
  (q3FrequencyCoordinate 0 ξ : ℂ) * F.fst ξ + (q3FrequencyCoordinate 1 ξ : ℂ) * F.snd ξ

theorem q3FrequencyCoordinate_memLp (h : ℝ) (i : Fin 2) :
    MemLp (q3FrequencyCoordinate i) 2 (q3SpectralMeasure h) := by
  apply (memLp_two_iff_integrable_sq (q3FrequencyCoordinate_continuous i).aestronglyMeasurable).mpr
  apply (q3SpectralMeasure_graphWeight_integrable h).mono'
    ((q3FrequencyCoordinate_continuous i).pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖(q3FrequencyCoordinate i ξ) ^ 2‖ ≤ 1 + ‖ξ‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact q3FrequencyCoordinate_sq_le i ξ

theorem q3SpectralRadialPairing_integrable (h : ℝ) (F : Q3SpectralVector h) :
    Integrable (q3SpectralRadialPairing h F) (q3SpectralMeasure h) :=
  ((q3FrequencyCoordinate_memLp h 0).ofReal.integrable_mul (Lp.memLp F.fst)).add
    ((q3FrequencyCoordinate_memLp h 1).ofReal.integrable_mul (Lp.memLp F.snd))

/-- The gradient pairing is the Fourier-testing pairing of the radial component. -/
theorem q3SpectralGradientMap_inner (h : ℝ)
    (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) (F : Q3SpectralVector h) :
    inner ℂ (q3SpectralGradientMap h p) F =
      ∫ ξ, q3SpectralRadialPairing h F ξ * (starRingEnd ℂ) (p ξ) ∂q3SpectralMeasure h := by
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, q3SpectralGradientMap_fst,
    q3SpectralGradientMap_snd, L2.inner_def]
  rw [← integral_add (L2.integrable_inner (q3SpectralGraphCoordinate h 0 p) F.fst)
    (L2.integrable_inner (q3SpectralGraphCoordinate h 1 p) F.snd)]
  apply integral_congr_ae
  filter_upwards [q3SpectralGraphCoordinate_coeFn h 0 p,
    q3SpectralGraphCoordinate_coeFn h 1 p] with ξ h0 h1
  rw [RCLike.inner_apply, RCLike.inner_apply, h0, h1]
  simp only [map_mul, Complex.conj_ofReal, q3SpectralRadialPairing]
  ring

/-- The orthogonal complement of the gradient range consists precisely of
fields perpendicular to the frequency almost everywhere. -/
theorem q3SpectralPotential_orthogonal_iff (h : ℝ) (F : Q3SpectralVector h) :
    F ∈ (q3SpectralPotentialSubspace h)ᗮ ↔
      q3SpectralRadialPairing h F =ᵐ[q3SpectralMeasure h] 0 := by
  rw [q3SpectralPotentialSubspace, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  constructor
  · intro hF
    apply ae_eq_zero_of_integral_mul_exp_eq_zero (q3SpectralRadialPairing_integrable h F)
    intro t
    let p : Lp ℂ 2 (q3SpectralGraphMeasure h) :=
      BoundedContinuousFunction.toLp 2 (q3SpectralGraphMeasure h) ℂ
        (BoundedContinuousFunction.innerProbChar (-t))
    have hp := ae_mono (q3SpectralMeasure_le_graphMeasure h)
      (BoundedContinuousFunction.coeFn_toLp 2 (q3SpectralGraphMeasure h) ℂ
        (BoundedContinuousFunction.innerProbChar (-t)))
    have hz := hF (q3SpectralGradientMap h p) ⟨p, rfl⟩
    rw [q3SpectralGradientMap_inner] at hz
    calc
      (∫ ξ, q3SpectralRadialPairing h F ξ * exp ((inner ℝ ξ t : ℂ) * I)
          ∂q3SpectralMeasure h) =
          ∫ ξ, q3SpectralRadialPairing h F ξ * (starRingEnd ℂ) (p ξ)
            ∂q3SpectralMeasure h := by
        apply integral_congr_ae
        filter_upwards [hp] with ξ hξ
        rw [hξ, BoundedContinuousFunction.innerProbChar_apply]
        simp only [inner_neg_right, ofReal_neg, neg_mul, ← Complex.exp_conj,
          map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul, mul_neg, neg_neg]
      _ = 0 := hz
  · intro hF G hG
    obtain ⟨p, rfl⟩ := hG
    change inner ℂ (q3SpectralGradientMap h p) F = 0
    rw [q3SpectralGradientMap_inner]
    calc
      (∫ ξ, q3SpectralRadialPairing h F ξ * (starRingEnd ℂ) (p ξ)
          ∂q3SpectralMeasure h) = ∫ _ : Q3FrequencyPlane, (0 : ℂ) ∂q3SpectralMeasure h := by
        apply integral_congr_ae
        filter_upwards [hF] with ξ hξ
        simp only [hξ, Pi.zero_apply, zero_mul]
      _ = 0 := integral_zero _ _

end ASDExplicitGamma.Model
