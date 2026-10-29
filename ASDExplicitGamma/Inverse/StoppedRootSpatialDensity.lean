module

public import ASDExplicitGamma.Inverse.StoppedRootConcentration
public import ASDExplicitGamma.Inverse.StoppedRootDensity
public import ASDExplicitGamma.Inverse.StoppedRootAverage

/-! Both source density bounds for the actual spatial average on every root layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Source (7.4) and PE for the genuine spatial average, at the actual mean
and for the positive excess above the rare-moment baseline. -/
theorem q3_root_spatial_density_bounds
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (R : ℕ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(R:ℤ), nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (hR : 60 ≤ R) (m : ℕ) (hm : m=2 ∨ m=4) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256)
    (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let B := q3PlanarMarks A (rootFineLabel Q R) τ (waveGateEta t)
    let X := rootDiameterAverage B Q R E m
    let v := (volume E).toReal/(volume (cubeSet Q)).toReal
    (eLpNorm (fun ω => X ω-∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (densityPEEnvelope q m p T R)) ∧
    (eLpNorm (fun ω => X ω-∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((3:ℝ)^(-(R:ℝ)/2))) ∧
    (eLpNorm (fun ω => max (X ω-v*densityMomentBudget q m T) 0) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (densityPEEnvelope q m p T R)) ∧
    (eLpNorm (fun ω => max (X ω-v*densityMomentBudget q m T) 0) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((3:ℝ)^(-(R:ℝ)/2))) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let B := q3PlanarMarks A (rootFineLabel Q R) τ (waveGateEta t)
  have hpast' : ∀ k ≤ rootFineLabel Q R+40, nativeInductionState A h k := by
    intro k hk
    apply hpast k
    unfold rootFineLabel at hk
    omega
  have hB : PlanarMarkControl μ B q :=
    q3_mark_control A h hA hg (rootFineLabel Q R) τ hτ t q hraw hpast'
  have hmpos : 1 ≤ m := by omega
  have hi (z : ↥(rootBlockPopulation Q R)) : Integrable (fun ω => (realDiameterField B z.val ω)^m) μ := by
    have hh := (real_diameter_nat_moment μ B q hB hq0 hq hfloor z.val (m-1) T hT hcut).1
    simpa only [show m-1+1=m by omega] using! hh
  have he := root_diameter_average_centered_eq μ B Q R E hE hEQ m hi
  have ha := root_diameter_average_eq B Q R E hE hEQ m
  have hPE := q3_root_density_PE A h hA hg Q R τ hτ t q hq0 hq hfloor hraw hpast
    T hT hcut hR m hmpos p hp hp256 E hE hEQ
  have hCon := q3_root_density_concentration A h hA hg Q R τ hτ t q hq0 hq hfloor hraw hpast
    T hT hcut hR m hm p hp hp256 E hE hEQ
  refine ⟨?_,?_,?_,?_⟩
  · change eLpNorm (fun ω => rootDiameterAverage B Q R E m ω-∫ ζ, rootDiameterAverage B Q R E m ζ ∂μ) _ μ ≤ _
    rw [he]
    exact hPE.1
  · change eLpNorm (fun ω => rootDiameterAverage B Q R E m ω-∫ ζ, rootDiameterAverage B Q R E m ζ ∂μ) _ μ ≤ _
    rw [he]
    exact hCon.1
  · change eLpNorm (fun ω => max (rootDiameterAverage B Q R E m ω-_) 0) _ μ ≤ _
    rw [ha]
    exact hPE.2
  · change eLpNorm (fun ω => max (rootDiameterAverage B Q R E m ω-_) 0) _ μ ≤ _
    rw [ha]
    exact hCon.2

end
end ASDExplicitGamma.Inverse
