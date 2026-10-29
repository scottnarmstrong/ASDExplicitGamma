module

public import ASDExplicitGamma.Inverse.StoppedDensityEstimates
public import ASDExplicitGamma.Inverse.StoppedRootBlockWeights

/-! Actual root-relative partial-volume density estimates on the physical q3 grid. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Both retained-power bounds for every measurable source layer in the root.
All weights and their total are the actual physical partial volumes. -/
theorem q3_root_density_PE
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (R : ℕ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(R:ℤ), nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (hR : 60 ≤ R) (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256)
    (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let B := q3PlanarMarks A (rootFineLabel Q R) τ (waveGateEta t)
    let w := fun z : ↥(rootBlockPopulation Q R) =>
      localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z.val)
    let v := (volume E).toReal/(volume (cubeSet Q)).toReal
    eLpNorm (fun ω => ∑ z, w z*((realDiameterField B z.val ω)^m-
      ∫ ζ, (realDiameterField B z.val ζ)^m ∂μ)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (densityPEEnvelope q m p T R) ∧
    eLpNorm (fun ω => max ((∑ z, w z*(realDiameterField B z.val ω)^m)-
      v*densityMomentBudget q m T) 0) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (densityPEEnvelope q m p T R) := by
  have hv := root_layer_fraction_bounds Q E hEQ
  have hpast' : ∀ k ≤ rootFineLabel Q R+40, nativeInductionState A h k := by
    intro k hk
    apply hpast k
    unfold rootFineLabel at hk
    omega
  exact q3_density_PE A h hA hg (rootFineLabel Q R) τ hτ t q hq0 hq hfloor
    hraw hpast' T hT hcut R hR m hm p hp hp256
    (fun z : ↥(rootBlockPopulation Q R) => z.val) Subtype.val_injective
    _ hv.1 hv.2 _ (fun z => localization_partial_weight_nonneg _ _ _)
    (fun z => root_partial_weight_le Q E R z.val)
    (root_partial_weights_sum Q E hE hEQ R)

end
end ASDExplicitGamma.Inverse
