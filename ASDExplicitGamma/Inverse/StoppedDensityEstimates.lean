module

public import ASDExplicitGamma.Inverse.StoppedFullDensity
public import ASDExplicitGamma.Inverse.StoppedDensityPE

/-! The actual q3 retained-power density estimate, with every source statistical input derived. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Actual PE at every effective depth R>=60 and real 2<=p<=256.
The deterministic weights retain their exact total v, including partial blocks.
No moment, independence, localization or density-concentration premise remains. -/
theorem q3_density_PE {I : Type} [Fintype I]
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (j : ℤ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ j+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (R : ℕ) (hR : 60 ≤ R) (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256)
    (x : I → BlockSite) (hx : Function.Injective x) (v : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hwmax : ∀ i, w i ≤ 9*(1/9:ℝ)^R) (hwv : ∑ i, w i = v) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let B := q3PlanarMarks A j τ (waveGateEta t)
    eLpNorm (fun ω => ∑ i, w i*((realDiameterField B (x i) ω)^m-
      ∫ ζ, (realDiameterField B (x i) ζ)^m ∂μ)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (densityPEEnvelope q m p T R) ∧
    eLpNorm (fun ω => max ((∑ i, w i*(realDiameterField B (x i) ω)^m)-
      v*densityMomentBudget q m T) 0) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (densityPEEnvelope q m p T R) := by
  have hh := q3_full_density_Lp A h hA hg j τ hτ t q hq0 hq hfloor hraw hpast T hT hcut
    (R/6+1) m hm p hp x hx ((1/9:ℝ)^R) v (by positivity) hv w hw hwmax hwv
  have hb := ENNReal.ofReal_le_ofReal (full_density_budget_le_PE q hq0 m p T
    (by linarith only [hp]) hp256 hT R hR v hv1)
  exact ⟨hh.1.trans hb,hh.2.trans hb⟩

end
end ASDExplicitGamma.Inverse
