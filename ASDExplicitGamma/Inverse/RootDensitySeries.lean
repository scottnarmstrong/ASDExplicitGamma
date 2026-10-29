module

public import ASDExplicitGamma.Inverse.RootDensityParameters
public import ASDExplicitGamma.Inverse.RootErrorMeasurable

/-! Both coarse and retained density bounds for the same actual positive
root density series, with the exact fixed-row parameters discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Literal positive density summand of the source. -/
def rootDensityTerm (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (rootEdelta r*rootResponseEnvelope (6*rootTau r))*
    resetDensityTerm2 M Q (rootH0 r) (rootTau r) (waveGateEta (rootWaveTuple r))
      (rootQ r) (rootMomentCutoff r) (planarGradientCharge 40) hk ω

private theorem scale_series_norm {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (F : I → Ω → ℝ) (c B : ℝ) (hc : 0 ≤ c)
    (hb : eLpNorm (fun ω => ∑' i, F i ω) p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => ∑' i, c*F i ω) p μ ≤ ENNReal.ofReal (c*B) := by
  have he : (fun ω => ∑' i, c*F i ω)=c • (fun ω => ∑' i, F i ω) := by
    funext ω
    exact tsum_mul_left
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hc,ENNReal.ofReal_mul hc]
  exact mul_le_mul_of_nonneg_left hb (zero_le : (0:ℝ≥0∞) ≤ _)

/-- Both source density alternatives hold for the same complete positive
actual series. Only the protected ordinary native past is a model premise. -/
theorem root_density_series_Lp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (r : RootRow)
    (hpast : ∀ k ≤ Q.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let F := rootDensityTerm M Q r
    (∀ᵐ ω ∂μ, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (rootDensityErrorBudget M.gamma r) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (rootDensityRetainedBudget M.gamma p r) := by
  obtain ⟨hH,hτ,hfloor,hT,hcut⟩ := root_row_density_parameters r
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs r
  let S := planarGradientCharge 40
  have hS : 0 ≤ S := by dsimp only [S,planarGradientCharge]; positivity
  let F := resetDensityTerm2 M Q (rootH0 r) (rootTau r) (waveGateEta (rootWaveTuple r))
    (rootQ r) (rootMomentCutoff r) S
  let c := rootEdelta r*rootResponseEnvelope (6*rootTau r)
  have hc : 0 ≤ c := by dsimp only [c,rootEdelta,rootResponseEnvelope]; positivity
  have hb := q3_reset_density_series2_bound M h hM hg Q _ hH _ hτ (rootWaveTuple r) _ hq0 hq hfloor hraw hpast
    _ hT hcut p hp hp256 S hS
  have hz := q3_reset_density_series2_coarse M h hM hg Q _ hH _ hτ (rootWaveTuple r) _ hq0 hq hfloor hraw hpast
    _ hT hcut p hp hp256 S hS
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hb.1] with ω hω
    change Summable (fun hk => ‖c*F hk ω‖)
    have hh := hω.mul_left |c|
    simpa only [norm_mul,Real.norm_eq_abs] using hh
  · exact scale_series_norm (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p) F c _ hc hz
  · exact scale_series_norm (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p) F c _ hc hb.2

end
end ASDExplicitGamma.Inverse
