module

public import ASDExplicitGamma.Inverse.StoppedUniformBernstein
public import ASDExplicitGamma.Inverse.StoppedUniformDensityBudget
public import ASDExplicitGamma.Inverse.StoppedLocalizationErrorLp
public import ASDExplicitGamma.Inverse.StoppedCenteredTransfer
public import ASDExplicitGamma.Inverse.StoppedPositiveCentering
public import ASDExplicitGamma.Inverse.StoppedDensityBudgets

/-! The actual full-field weighted density estimate, before retained-power optimization. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Both source density quantities for the actual q3 diameter field: centering
at its actual mean, and the positive part after subtracting the moment cap.
Every statistical input is derived from the model and protected native past. -/
theorem q3_full_uniform_density_Lp {I : Type} [Fintype I]
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (j : ℤ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ j+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (M m : ℕ) (hm : m=2 ∨ m=4) (p : ℝ) (hp : 2 ≤ p)
    (x : I → BlockSite) (hx : Function.Injective x)
    (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwmax : ∀ i, w i ≤ 9*a) (hwv : ∑ i, w i = v) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let B := q3PlanarMarks A j τ (waveGateEta t)
    eLpNorm (fun ω => ∑ i, w i*((realDiameterField B (x i) ω)^m-
      ∫ ζ, (realDiameterField B (x i) ζ)^m ∂μ)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (uniformDensityBudget m p M a v) ∧
    eLpNorm (fun ω => max ((∑ i, w i*(realDiameterField B (x i) ω)^m)-
      v*densityMomentBudget q m T) 0) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (uniformDensityBudget m p M a v) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let B := q3PlanarMarks A j τ (waveGateEta t)
  let X : I → Cutoff.CutoffSample 2 → ℝ := fun i ω => (realDiameterField B (x i) ω)^m
  let Y : I → Cutoff.CutoffSample 2 → ℝ := fun i ω => (realLocalizedDiameterField B M (3^M) (x i) ω)^m
  have hB : PlanarMarkControl μ B q := q3_mark_control A h hA hg j τ hτ t q hraw hpast
  have hmpos : 1 ≤ m := by omega
  have hβ0 : 0 ≤ uniformDensityVariance m := by unfold uniformDensityVariance; split <;> norm_num
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hm1 : m-1+1 = m := by omega
  have hMom (i : I) : Integrable (X i) μ ∧ (∫ ω, X i ω ∂μ) ≤ densityMomentBudget q m T := by
    have hh := real_diameter_nat_moment μ B q hB hq0 hq hfloor (x i) (m-1) T hT hcut
    simpa only [hm1] using! hh
  have hiY (i : I) : Integrable (Y i) μ :=
    localized_diameter_power_integrable μ B hB.local_measurable hB.positive_measurable M (3^M) (x i) m
  have hX (i : I) : Measurable (X i) :=
    (real_diameter_measurable B hB.local_measurable hB.positive_measurable (x i)).pow_const m
  have herror (i : I) : eLpNorm (fun ω => X i ω-Y i ω) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (localizationErrorBudget m p M) :=
    localization_power_error_Lp μ B q hB hq0 hq hfloor M m hmpos (x i) p hp1
  have hLoc : eLpNorm (fun ω => ∑ i, w i*(Y i ω-∫ ζ, Y i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((4*Real.sqrt (p*21^2*uniformDensityVariance m*(3:ℝ)^(2*M)*a*v)+4*p*21^2*4^m*(3:ℝ)^(M*(m+2))*a)) :=
    q3_localized_uniform_block_Lp A h hA hg j τ hτ t q hq0 hq hfloor hraw hpast
      M m hm p hp x hx a v ha hv w hw hwmax hwv
  have hC := localization_error_budget_nonneg m p (by linarith only [hp]) M
  have htransfer := weighted_centered_transfer μ X Y (fun i => (hMom i).1) hiY w hw
    (localizationErrorBudget m p M) p hC hp1 herror
  rw [hwv] at htransfer
  have hLoc0 : 0 ≤ (4*Real.sqrt (p*21^2*uniformDensityVariance m*(3:ℝ)^(2*M)*a*v)+4*p*21^2*4^m*(3:ℝ)^(M*(m+2))*a) := by
    positivity
  have hfull : eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p M a v) := by
    apply htransfer.trans
    apply (add_le_add hLoc le_rfl).trans_eq
    exact (ENNReal.ofReal_add hLoc0 (by positivity)).symm
  exact ⟨hfull,(weighted_positive_excess_le_centered μ X hX w hw v
    (densityMomentBudget q m T) hwv (fun i => (hMom i).2) (ENNReal.ofReal p)).trans hfull⟩

end
end ASDExplicitGamma.Inverse
