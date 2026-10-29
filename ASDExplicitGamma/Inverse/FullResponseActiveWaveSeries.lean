module

public import ASDExplicitGamma.Inverse.FullResponseIdentityWaveSeries
public import ASDExplicitGamma.Inverse.FullResponsePhysicalSelectedWave
public import ASDExplicitGamma.Inverse.FullResponseLayerEndpoint

/-! Actual selected active-wave layer payments with corrected positive weights. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Actual active root-fourth-moment wave, with its exact square-root layer volume. -/
def fullResponseActiveWaveTerm (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H := rootSelectedHeight M Q .full ω
  let x := (localizationResetAbscissa (377-38) (H-377) k:ℝ)
  Real.sqrt (bankLayerWeight k)*((3:ℝ)^(2*M.gamma*x)*
    fullResponseLayerWaveFourth M Q 377 (H-377,k) (Q.scale-342) N weights ω)

/-- The corrected positive source layer envelope for the actual active wave. -/
def fullResponseActiveWaveTermBudget (γ p D : ℝ) (k : ℕ) : ℝ :=
  (γ*(3:ℝ)^(2*γ*D)/2)*fullResponseRootLayerEnvelope k*
    (Numerics.Inverse.invLayerZ:ℝ)^localizationProfileDepth (k+1)*
      ((D+(localizationProfileDepth (k+1):ℝ))*physicalSelectedWaveBudget γ p 377 0+
        physicalSelectedWaveBudget γ p 377 1)

/-- Each actual selected identity layer has the exact source scalar payment. -/
theorem full_response_active_wave_term_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (k : ℕ) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    Measurable (fullResponseActiveWaveTerm M Q N weights k) ∧
      eLpNorm (fullResponseActiveWaveTerm M Q N weights k) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
          (fullResponseActiveWaveTermBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) k) := by
  let H := rootSelectedHeight M Q .full
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  let f := (localizationProfileDepth (k+1):ℝ)
  let C := (M.gamma*(3:ℝ)^(2*M.gamma*D)/2)*Real.sqrt (bankLayerWeight k)*(3:ℝ)^(4*M.gamma*f)
  let W := fun j : Fin 2 => fun ω => physicalHeightWeightedWave M Q N 377
    (cubeCorner Q 0) (cubeCorner Q 1)
    (fun _ => sourceBandWeights (Q.scale-342) weights) k j (H ω) ω
  have hH : Measurable H := q3_stopped_height_measurable M Q 377 (rootTau .full)
    (waveGateEta (rootWaveTuple .full))
  have hm (j : Fin 2) : Measurable (W j) :=
    full_response_selected_family_measurable H hH _
      (physical_height_weighted_wave_measurable M Q N 377 _ _ _ k j)
  have hb (j : Fin 2) := full_response_physical_selected_wave_Lp M h hM hg Q hpast
    N hN weights hw k j p hp hp256
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hDf : 0 ≤ D+f := add_nonneg hD (Nat.cast_nonneg _)
  have hC : 0 ≤ C := by
    have hγ := M.shellPrefix.gamma_pos.le
    have hv := Real.sqrt_nonneg (bankLayerWeight k)
    dsimp only [C]
    positivity
  have he : fullResponseActiveWaveTerm M Q N weights k =
      fun ω => (C*(D+f))*W 0 ω+C*W 1 ω := by
    funext ω
    have hge : 377 ≤ H ω := q3_stopped_height_ge M Q 377 (rootTau .full)
      (waveGateEta (rootWaveTuple .full)) ω
    have hh := full_response_height_layer_wave_reconstruction M Q 377 (H ω) k
      (by norm_num) hge (Q.scale-342) N hN weights ω
    dsimp only [fullResponseActiveWaveTerm]
    rw [hh]
    simp only [W,physicalHeightWeightedWave,Fin.val_zero,pow_zero,one_mul]
    dsimp only [C,D,f]
    ring
  rw [he]
  refine ⟨((hm 0).const_mul _).add ((hm 1).const_mul _), ?_⟩
  have hh := full_response_linear_family_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) (W 0) (W 1)
    (C*(D+f)) C (physicalSelectedWaveBudget M.gamma p 377 0)
    (physicalSelectedWaveBudget M.gamma p 377 1) (mul_nonneg hC hDf) hC
    (full_response_selected_wave_budget_nonneg _ _ (by linarith only [hp]) _)
    (full_response_selected_wave_budget_nonneg _ _ (by linarith only [hp]) _) (hb 0) (hb 1)
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hclock := full_response_root_layer_clock_le M.gamma hg k
  have hfac : C ≤ (M.gamma*(3:ℝ)^(2*M.gamma*D)/2)*fullResponseRootLayerEnvelope k*
      (Numerics.Inverse.invLayerZ:ℝ)^localizationProfileDepth (k+1) := by
    have hγ := M.shellPrefix.gamma_pos.le
    have hh := mul_le_mul_of_nonneg_left hclock
      (show 0 ≤ M.gamma*(3:ℝ)^(2*M.gamma*D)/2 by positivity)
    dsimp only [C,f]
    convert hh using 1 <;> ring
  have h0 := full_response_selected_wave_budget_nonneg M.gamma p (by linarith only [hp]) 0
  have h1 := full_response_selected_wave_budget_nonneg M.gamma p (by linarith only [hp]) 1
  have hnonneg : 0 ≤ (D+f)*physicalSelectedWaveBudget M.gamma p 377 0+
      physicalSelectedWaveBudget M.gamma p 377 1 := by positivity
  have hh' := mul_le_mul_of_nonneg_right hfac hnonneg
  dsimp only [fullResponseActiveWaveTermBudget]
  dsimp only [f] at hh'
  convert hh' using 1
  ring

/-- Exact summation of the corrected positive active-wave envelope. -/
theorem full_response_active_wave_budget_hasSum (γ p D : ℝ) :
    HasSum (fullResponseActiveWaveTermBudget γ p D)
      ((γ*(3:ℝ)^(2*γ*D)/2)*
        (physicalSelectedWaveBudget γ p 377 0*
          (D*(Numerics.Inverse.invL0plus:ℝ)+(Numerics.Inverse.invL1plus:ℝ))+
            physicalSelectedWaveBudget γ p 377 1*(Numerics.Inverse.invL0plus:ℝ))) := by
  obtain ⟨h0,h1⟩ := full_response_root_layer_endpoint_profiles
  have hh := (((h0.mul_left D).add h1).mul_left
    (physicalSelectedWaveBudget γ p 377 0)).add
      (h0.mul_left (physicalSelectedWaveBudget γ p 377 1))
  convert hh.mul_left (γ*(3:ℝ)^(2*γ*D)/2) using 1
  funext k
  dsimp only [fullResponseActiveWaveTermBudget]
  ring

/-- Complete actual active leading-wave series, with the source corrected
L0plus/L1plus combination and no selected-height independence premise. -/
theorem full_response_active_wave_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    let F := fullResponseActiveWaveTerm M Q N weights
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, Summable (fun k => ‖F k ω‖)) ∧
      eLpNorm (fun ω => ∑' k, F k ω) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
          ((M.gamma*(3:ℝ)^(2*M.gamma*D)/2)*
            (physicalSelectedWaveBudget M.gamma p 377 0*
              (D*(Numerics.Inverse.invL0plus:ℝ)+(Numerics.Inverse.invL1plus:ℝ))+
                physicalSelectedWaveBudget M.gamma p 377 1*(Numerics.Inverse.invL0plus:ℝ))) := by
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  have hb (k : ℕ) := full_response_active_wave_term_Lp M h hM hg Q hpast N hN weights hw k p hp hp256
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hc (k : ℕ) : 0 ≤ fullResponseActiveWaveTermBudget M.gamma p D k := by
    have hγ := M.shellPrefix.gamma_pos.le
    have hv : 0 ≤ fullResponseRootLayerEnvelope k :=
      (Real.sqrt_nonneg _).trans (full_response_root_layer_sqrt_le k)
    have hz : (0:ℝ) ≤ (Numerics.Inverse.invLayerZ:ℝ) := by
      norm_num [Numerics.Inverse.invLayerZ,Numerics.Inverse.invE,Numerics.Inverse.invGamma]
    have h0 := full_response_selected_wave_budget_nonneg M.gamma p (by linarith only [hp]) 0
    have h1 := full_response_selected_wave_budget_nonneg M.gamma p (by linarith only [hp]) 1
    dsimp only [fullResponseActiveWaveTermBudget]
    positivity
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (fullResponseActiveWaveTerm M Q N weights) (fun k => (hb k).1)
    (fullResponseActiveWaveTermBudget M.gamma p D) hc _
    (full_response_active_wave_budget_hasSum M.gamma p D)
    (fun k => (hb k).2)

end
end ASDExplicitGamma.Inverse
