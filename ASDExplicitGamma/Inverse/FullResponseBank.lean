module

public import ASDExplicitGamma.Inverse.FullResponseFrameTransport

/-! Complete full-response banks in arbitrary true frames. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Actual normalized full response with the exact certified order-64 row. -/
theorem full_response_bank64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N K : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N K weights ω/4)
      (ENNReal.ofReal 64) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        (((invFull64Bt:ℝ)+M.gamma*((invFull64KD:ℝ)*D+(invFull64K0:ℝ)))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  dsimp only
  have ht := full_response_trace_frame_Lp_le M Q (Q.scale-342) N K (by omega) weights (ENNReal.ofReal 64)
  have hr := full_response_reference64 M h hM hg Q hpast N hN weights hw
  apply (ht.trans (mul_le_mul' le_rfl hr)).trans
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_add (by norm_num : (0:ℝ)<3)]
  exact le_of_eq (by ring)

/-- Audited outward order-64 cap for the actual normalized full response. -/
theorem full_response_bank64_outward
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N K : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N K weights ω/4)
      (ENNReal.ofReal 64) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((2018618/1000000+M.gamma*(16684*D+5899542))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  apply (full_response_bank64 M h hM hg Q hpast N K hN weights hw).trans
  apply ENNReal.ofReal_le_ofReal
  have hD : (0:ℝ) ≤ (N:ℝ)-(Q.scale:ℝ)+1 := by exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  exact mul_le_mul_of_nonneg_right
    (full_response_profile_64_outward M.gamma _ M.shellPrefix.gamma_pos.le hD)
    (Real.rpow_nonneg (by norm_num) _)

/-- Actual normalized full response with the exact certified order-128 row. -/
theorem full_response_bank128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N K : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N K weights ω/4)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        (((invFull128Bt:ℝ)+M.gamma*((invFull128KD:ℝ)*D+(invFull128K0:ℝ)))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  dsimp only
  have ht := full_response_trace_frame_Lp_le M Q (Q.scale-342) N K (by omega) weights (ENNReal.ofReal 128)
  have hr := full_response_reference128 M h hM hg Q hpast N hN weights hw
  apply (ht.trans (mul_le_mul' le_rfl hr)).trans
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_add (by norm_num : (0:ℝ)<3)]
  exact le_of_eq (by ring)

/-- Audited outward order-128 cap for the actual normalized full response. -/
theorem full_response_bank128_outward
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N K : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N K weights ω/4)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((2018618/1000000+M.gamma*(32474*D+11483216))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  apply (full_response_bank128 M h hM hg Q hpast N K hN weights hw).trans
  apply ENNReal.ofReal_le_ofReal
  have hD : (0:ℝ) ≤ (N:ℝ)-(Q.scale:ℝ)+1 := by exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  exact mul_le_mul_of_nonneg_right
    (full_response_profile_128_outward M.gamma _ M.shellPrefix.gamma_pos.le hD)
    (Real.rpow_nonneg (by norm_num) _)

end
end ASDExplicitGamma.Inverse
