module

public import ASDExplicitGamma.Inverse.FullResponseSelectedScalarLayer
public import ASDExplicitGamma.Inverse.RootDensityParameters

/-! Model-discharged full-row density and correlated-error series. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Complete actual full-row D2 series, with all model and gate inputs discharged. -/
theorem full_response_density_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let F := fullResponseDensityTerm M Q
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
          (densityD2 (rootQ .full) p 1232 M.gamma (planarGradientCharge 40) (377-38)) := by
  obtain ⟨hH,hτ,hfloor,hT,hcut⟩ := root_row_density_parameters .full
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  have hprotected : ∀ k ≤ Q.scale-(377:ℤ)+40, nativeInductionState M h k := by
    intro k hk
    apply hpast k
    omega
  exact q3_reset_density_series2_bound M h hM hg Q 377 hH (rootTau .full) hτ
    .full (rootQ .full) hq0 hq hfloor hraw hprotected 1232 hT hcut p hp hp256
    (planarGradientCharge 40) (by unfold planarGradientCharge; positivity)

/-- Both full-row correlated D4 error series with their literal depth moments. -/
theorem full_response_correlated_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights k ∧ weights k ≤ 1)
    (j : Fin 2) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let F := fullResponseCorrelatedTerm M Q N weights j
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
          (40*(2*p+2)*(if j=0 then densityD40 (rootQ .full) p 1232 M.gamma
            (planarGradientCharge 40) (377-38) else densityD41 (rootQ .full) p 1232 M.gamma
              (planarGradientCharge 40) (377-38))) := by
  obtain ⟨hH,hτ,hfloor,hT,hcut⟩ := root_row_density_parameters .full
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  have hprotected : ∀ k ≤ Q.scale-(377:ℤ)+40, nativeInductionState M h k := by
    intro k hk
    apply hpast k
    omega
  exact full_response_correlated_density_series_Lp M h hM hg Q N hN 377 hH
    (rootTau .full) hτ .full (rootQ .full) hq0 hq hfloor hraw hprotected 1232 hT hcut
    (cubeCorner Q 0) (cubeCorner Q 1) _
    (fun hk => source_band_weights_bounds _ _ N weights hw) p hp hp256
    (planarGradientCharge 40) (by unfold planarGradientCharge; positivity) j

/-- The same actual D2 series also obeys the source coarse e_Z envelope. -/
theorem full_response_density_series_coarse_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    eLpNorm (fun ω => ∑' hk, fullResponseDensityTerm M Q hk ω) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (densityEZ M.gamma (planarGradientCharge 40) (377-38)) := by
  obtain ⟨hH,hτ,hfloor,hT,hcut⟩ := root_row_density_parameters .full
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  exact q3_reset_density_series2_coarse M h hM hg Q 377 hH (rootTau .full) hτ
    .full (rootQ .full) hq0 hq hfloor hraw (by intro k hk; apply hpast k; omega)
    1232 hT hcut p hp hp256 (planarGradientCharge 40) (by unfold planarGradientCharge; positivity)

end
end ASDExplicitGamma.Inverse
