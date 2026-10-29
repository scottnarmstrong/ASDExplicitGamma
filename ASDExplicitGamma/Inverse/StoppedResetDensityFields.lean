module

public import ASDExplicitGamma.Inverse.StoppedRootSpatialDensity
public import ASDExplicitGamma.Inverse.WeightedLocalizationWhitneyWeights
public import ASDExplicitGamma.Inverse.WeightedLocalizationResetSeries

/-! Actual density excesses at every deterministic protected reset height and resolution. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The exact three effective density depths x_{kh}+1-e, with e=0,1,2. -/
def resetDensityDepth (H0 : ℕ) (hk : ℕ × ℕ) (e : Fin 3) : ℕ :=
  localizationResetAbscissa (H0-38) hk.1 hk.2+1-e.val

/-- Every source reset resolution is beyond the density entrance. -/
theorem reset_density_depth_lower (H0 : ℕ) (hH : 333 ≤ H0) (hk : ℕ × ℕ) (e : Fin 3) :
    60 ≤ resetDensityDepth H0 hk e ∧ H0-40 ≤ resetDensityDepth H0 hk e := by
  have he := e.isLt
  unfold resetDensityDepth localizationResetAbscissa localizationProfileDepth
  omega

/-- Exact real abscissa identity, without truncated subtraction. -/
theorem reset_density_depth_real (H0 : ℕ) (hk : ℕ × ℕ) (e : Fin 3) :
    (resetDensityDepth H0 hk e:ℝ) =
      (localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1-(e.val:ℝ) := by
  have he : e.val ≤ localizationResetAbscissa (H0-38) hk.1 hk.2+1 := by
    have hlt := e.isLt
    unfold localizationResetAbscissa localizationProfileDepth
    omega
  rw [resetDensityDepth,Nat.cast_sub he,Nat.cast_add,Nat.cast_one]

/-- Protected native past suffices simultaneously for every height, layer
and resolution; no random selected-height substitution is used here. -/
theorem reset_density_past (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (hk : ℕ × ℕ) (e : Fin 3) (k : ℤ)
    (hk' : k ≤ Q.scale-(resetDensityDepth H0 hk e:ℤ)) :
    k ≤ Q.scale-(H0:ℤ)+40 := by
  have hd := (reset_density_depth_lower H0 hH hk e).2
  omega

/-- Positive source density excess on the literal translated Whitney layer,
using its exact v_k rather than a geometric envelope. -/
def resetDensityExcess (A : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ)
    (τ η q T : ℝ) (m : ℕ) (hk : ℕ × ℕ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let R := resetDensityDepth H0 hk e
  let B := q3PlanarMarks A (rootFineLabel Q R) τ η
  max (rootDiameterAverage B Q R (localizationWhitneyLayer Q (H0+hk.1) hk.2) m ω-
    bankLayerWeight hk.2*densityMomentBudget q m T) 0

theorem reset_density_excess_nonneg (A : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ)
    (τ η q T : ℝ) (m : ℕ) (hk : ℕ × ℕ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) :
    0 ≤ resetDensityExcess A Q H0 τ η q T m hk e ω := le_max_right _ _

/-- Both source density norms at every protected reset, on the actual q3
sample space and with the exact physical Whitney layer volume. -/
theorem q3_reset_density_bounds
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ)
    (t : WaveGateTuple) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (m : ℕ) (hm : m=2 ∨ m=4) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256)
    (hk : ℕ × ℕ) (e : Fin 3) :
    let Y := resetDensityExcess A Q H0 τ (waveGateEta t) q T m hk e
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    Measurable Y ∧
      eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (densityPEEnvelope q m p T (resetDensityDepth H0 hk e)) ∧
      eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((3:ℝ)^(-(resetDensityDepth H0 hk e:ℝ)/2)) := by
  let R := resetDensityDepth H0 hk e
  let E := localizationWhitneyLayer Q (H0+hk.1) hk.2
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let B := q3PlanarMarks A (rootFineLabel Q R) τ (waveGateEta t)
  have hE : MeasurableSet E := localization_whitney_layer_measurable Q _ _
  have hEQ : E ⊆ cubeSet Q := localization_whitney_layer_subset Q _ _
  have hpast' : ∀ k ≤ Q.scale-(R:ℤ), nativeInductionState A h k := by
    intro k hk'
    exact hpast k (reset_density_past Q H0 hH hk e k hk')
  have hB : PlanarMarkControl μ B q := by
    apply q3_mark_control A h hA hg (rootFineLabel Q R) τ hτ t q hraw
    intro k hk'
    apply hpast' k
    unfold rootFineLabel at hk'
    omega
  have hy : Measurable (resetDensityExcess A Q H0 τ (waveGateEta t) q T m hk e) :=
    ((root_diameter_average_measurable B hB.local_measurable hB.positive_measurable Q R E hE hEQ m).sub
      measurable_const).max measurable_const
  have hh := q3_root_spatial_density_bounds A h hA hg Q R τ hτ t q hq0 hq hfloor hraw hpast'
    T hT hcut (reset_density_depth_lower H0 hH hk e).1 m hm p hp hp256 E hE hEQ
  have hv : (volume E).toReal/(volume (cubeSet Q)).toReal = bankLayerWeight hk.2 :=
    localization_whitney_layer_volume Q _ _
  rw [hv] at hh
  exact ⟨hy,hh.2.2.1,hh.2.2.2⟩

end
end ASDExplicitGamma.Inverse
