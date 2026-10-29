module

public import ASDExplicitGamma.Inverse.FullResponseTraceScalarSeries
public import ASDExplicitGamma.Inverse.FullResponseIdentityWaveSeries
public import ASDExplicitGamma.Inverse.FullResponseActiveWaveSeries
public import ASDExplicitGamma.Inverse.FullResponseCorrelatedDensity
public import ASDExplicitGamma.Inverse.StoppedResetDensitySeries2

/-! Exact selected full-response scalar-layer decomposition into source suppliers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The full-row actual D2 error, summed over deterministic heights later. -/
def fullResponseDensityTerm (M : ABKModel 2) (Q : TriadicCube 2)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  resetDensityTerm2 M Q 377 (rootTau .full) (waveGateEta .full)
    (rootQ .full) 1232 (planarGradientCharge 40) hk ω

/-- The full-row actual correlated wave-density error, with both exact depth moments. -/
def fullResponseCorrelatedTerm (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (j : Fin 2) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  physicalCorrelatedDensityTerm M Q N 377 (rootTau .full) (waveGateEta .full)
    (rootQ .full) 1232 (planarGradientCharge 40) (cubeCorner Q 0) (cubeCorner Q 1)
    (fun _ => sourceBandWeights (Q.scale-342) weights) j hk ω

/-- Each actual selected scalar layer is exactly the sum of its baseline,
identity and active leading waves, matrix, D2 and correlated D4 payments.
No independence or moment bound is a premise of this algebraic identity. -/
theorem full_response_selected_scalar_layer_eq
    (M : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (hN : Q.scale-1 ≤ N)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (i : ℕ) :
    let H := rootSelectedHeight M Q .full ω
    let hk := (H-377,i)
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    fullResponseTraceScalarLayer M Q hk N weights ω =
      rootEdelta .full*fullResponseTraceBaseline*rootAssemblyClock M.gamma H (i+1)*bankLayerWeight i+
      (rootEdelta .full*(29/25:ℝ))*fullResponseIdentityWaveTerm M Q N weights i ω+
      (rootEdelta .full*3*(planarGradientCharge 40+1)*fullResponseTraceC1*
        Real.sqrt (densityMomentBudget (rootQ .full) 4 1232))*
          fullResponseActiveWaveTerm M Q N weights i ω+
      fullResponseTraceMatrixTerm M Q 377 N (sourceBandWeights (Q.scale-342) weights) hk ω+
      (rootEdelta .full*fullResponseTraceC0)*fullResponseDensityTerm M Q hk ω+
      (rootEdelta .full*fullResponseTraceC1*M.gamma*(3:ℝ)^(2*M.gamma*D)/2)*
        (D*fullResponseCorrelatedTerm M Q N weights 0 hk ω+
          fullResponseCorrelatedTerm M Q N weights 1 hk ω) := by
  dsimp only
  let H := rootSelectedHeight M Q .full ω
  let hk : ℕ × ℕ := (H-377,i)
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  let x := (localizationResetAbscissa (377-38) hk.1 hk.2:ℝ)
  have hH : 377 ≤ H := q3_stopped_height_ge M Q 377 (rootTau .full)
    (waveGateEta (rootWaveTuple .full)) ω
  have hadd : 377+hk.1=H := by dsimp only [hk]; omega
  have hclock : rootAssemblyClock M.gamma H (i+1)=(3:ℝ)^(2*M.gamma*x) := by
    have hh := assembly_clock_eq_reset M.gamma 377 (by norm_num) hk
    simpa only [hadd,hk,x] using hh
  have hreset := full_response_layer_wave_reconstruction M Q 377 (by norm_num)
    hk (Q.scale-342) N hN weights ω
  change (3:ℝ)^(2*M.gamma*x)*fullResponseLayerWaveFourth M Q 377 hk (Q.scale-342) N weights ω =
    (M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*D)/2)*
      physicalResetWave M Q N 377 (cubeCorner Q 0) (cubeCorner Q 1)
        (fun _ => sourceBandWeights (Q.scale-342) weights) hk ω at hreset
  have hcross := congrArg (fun z : ℝ => z*(planarGradientCharge 40+1)*
    (∑ e : Fin 3, Real.sqrt (resetDensityExcess M Q 377 (rootTau .full)
      (waveGateEta .full) (rootQ .full) 1232 4 hk e ω))) hreset
  dsimp only [fullResponseTraceScalarLayer,fullResponseIdentityWaveTerm,
    fullResponseActiveWaveTerm,fullResponseTraceMatrixTerm,fullResponseDensityTerm,
    resetDensityTerm2,fullResponseCorrelatedTerm,physicalCorrelatedDensityTerm]
  simp only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one]
  rw [hadd,hclock]
  dsimp only [H,hk,D,x] at hcross ⊢
  simp only [← Finset.mul_sum] at hcross ⊢
  linear_combination (rootEdelta .full*fullResponseTraceC1)*hcross

end
end ASDExplicitGamma.Inverse
