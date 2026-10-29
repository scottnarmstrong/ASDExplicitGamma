module

public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport

/-! Full-cutoff and completed-base full-response exports. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Outward order-64 bank for any completed base above the protected label.
The only native-state prefix is the source target n≤N-303. -/
theorem full_response_completed_bank64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (N K m : ℤ) (hN : Q.scale-1 ≤ N) (hm : Q.scale-342 ≤ m) (hmN : m ≤ N)
    (hpast : ∀ n ≤ N-303, nativeInductionState M h n)
    (weights : ℤ → ℝ) (hw : ∀ j ∈ Finset.Ioc m N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q m N K weights ω/4)
      (ENNReal.ofReal 64) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((2018618/1000000+M.gamma*(16684*D+5899542))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  have hh := full_response_bank64_outward M h hM hg Q
    (fun n hn => hpast n (by omega)) N K hN (sourceBandWeights m weights)
    (source_band_weights_bounds (Q.scale-342) m N weights hw)
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) N K (sourceBandWeights m weights) ω/4) =
      (fun ω => rootTraceObservable M Q m N K weights ω/4) := by
    funext ω
    unfold rootTraceObservable
    rw [full_response_coefficient_promote M _ m N hm hmN]
  rw [he] at hh
  exact hh

/-- The actual full terminal cutoff satisfies the order-64 source bank,
with the exact quarter normalization and root-relative clock. -/
theorem full_response_cutoff_bank64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (N K : ℤ) (hN : Q.scale-1 ≤ N)
    (hpast : ∀ n ≤ N-303, nativeInductionState M h n) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M K:ℝ)
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω))))/4)
      (ENNReal.ofReal 64) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((2018618/1000000+M.gamma*(16684*D+5899542))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  have hh := full_response_bank64_outward M h hM hg Q
    (fun n hn => hpast n (by omega)) N K hN (fun _ => 1) (by intros; norm_num)
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) N K (fun _ => 1) ω/4) =
      (fun ω => Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M K:ℝ)
        (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω))))/4) := by
    funext ω
    unfold rootTraceObservable
    rw [full_response_coefficient_unit M _ N (by omega)]
  rw [he] at hh
  exact hh

/-- Outward order-128 bank for any completed base above the protected label.
The only native-state prefix is the source target n≤N-303. -/
theorem full_response_completed_bank128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (N K m : ℤ) (hN : Q.scale-1 ≤ N) (hm : Q.scale-342 ≤ m) (hmN : m ≤ N)
    (hpast : ∀ n ≤ N-303, nativeInductionState M h n)
    (weights : ℤ → ℝ) (hw : ∀ j ∈ Finset.Ioc m N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q m N K weights ω/4)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((2018618/1000000+M.gamma*(32474*D+11483216))*
          (3:ℝ)^(2*M.gamma*D+2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)) := by
  have hh := full_response_bank128_outward M h hM hg Q
    (fun n hn => hpast n (by omega)) N K hN (sourceBandWeights m weights)
    (source_band_weights_bounds (Q.scale-342) m N weights hw)
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) N K (sourceBandWeights m weights) ω/4) =
      (fun ω => rootTraceObservable M Q m N K weights ω/4) := by
    funext ω
    unfold rootTraceObservable
    rw [full_response_coefficient_promote M _ m N hm hmN]
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Inverse
