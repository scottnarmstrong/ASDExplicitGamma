module

public import ASDExplicitGamma.Native.ReturnsHeatTable
public import ASDExplicitGamma.Native.ReturnsFrame
public import ASDExplicitGamma.Native.HeatStepNodeClosed
public import ASDExplicitGamma.Main.FrameEndpoint
public import ASDExplicitGamma.Main.FrameAlgebra
public import ASDExplicitGamma.Statements.BufferMean

/-! NA-RETURNS: the buffer mean `E T(Q_{N-40}; a_N, σ̄_N)` from the heat mean at `g = 49` and the
mean frame restoration (`E T_true ≤ ρ E T_old`). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational ASDExplicitGamma.Main
open scoped ENNReal

/-- The mean restoration from the old frame `σ̄_K` to `σ̄_{K+g}` on a cube. -/
theorem nativeReturns_mean_frame (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (K : ℤ) (g : ℕ)
    (hg1334 : g ≤ 1334) (q : ℤ) :
    ∫ ω, cutoffTraceDefect M (K + (g : ℤ)) q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (1 / (1 - (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ))) *
        ∫ ω, traceDefect (cubeSet (originCube 2 q))
          (Cutoff.coefficientCutoff M.nu (K + (g : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hold := (Annealed.sigmaBar_characterization M K).1
  have hc := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M K g
  have hR := (hc.2).trans (nativeReturns_ratio_le M hg g hg1334)
  have hmain := main_completed_frame_return_of_ratio M (K + (g : ℤ)) q (Annealed.sigmaBar M K : ℝ)
    _ hold hc.1 hR
  rw [main_completed_trace_integral_eq, main_completed_trace_integral_eq] at hmain
  exact hmain

theorem nativeReturns_bufferMean (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgam : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    bufferMean M N ≤ ENNReal.ofReal
      ((((nativeE (98 * nativeGamma) : ℚ)) : ℝ) * (((nativeHeat049Result.2 : ℚ)) : ℝ)) := by
  haveI : NeZero 49 := ⟨by norm_num⟩
  set m : ℤ := N - 50 with hm
  have hpast : ∀ j < m + 1, nativeInductionState M h j := fun j hj => hN j (by omega)
  have hstate : nativeInductionState M h (m + 1) := hN _ (by omega)
  have hheat := (nativeRefinedHeatStep_Gen_closed 49 (by norm_num) (by norm_num) M h hM hgam m
    hpast hstate).2
  rw [nativeHeatResultGen_049] at hheat
  have hmean := nativeReturns_mean_frame M hgam (m + 1) 49 (by norm_num) (m + 10)
  have e1 : m + 1 + ((49 : ℕ) : ℤ) = N := by rw [hm]; push_cast; ring
  have e2 : m + 10 = N - 40 := by rw [hm]; ring
  rw [e1, e2] at hmean
  have hR0 : (1 / (1 - (((11 / 10) * (2 * nativeGamma * ((49 : ℕ) : ℚ)) : ℚ) : ℝ))) =
      (((nativeE (98 * nativeGamma) : ℚ)) : ℝ) := by
    norm_num [nativeE, nativeGamma]
  rw [hR0] at hmean
  have hold : ∫ ω, traceDefect (cubeSet (originCube 2 (N - 40)))
      (Cutoff.coefficientCutoff M.nu N ω).toFun (Annealed.sigmaBar M (m + 1) : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ((nativeHeat049Result.2 : ℚ) : ℝ) := by
    have := hheat
    unfold nativeHeatStepParentTrace at this
    rw [show m + 1 + ((49 : ℕ) : ℤ) = N from e1, show m + 10 = N - 40 from e2] at this
    exact this
  have hE0 : (0 : ℝ) ≤ (((nativeE (98 * nativeGamma) : ℚ)) : ℝ) := by
    norm_num [nativeE, nativeGamma]
  have hfin := hmean.trans (mul_le_mul_of_nonneg_left hold hE0)
  unfold bufferMean
  rw [← ofReal_integral_eq_lintegral_ofReal
    (ASDExplicitGamma.Cold.integrable_cutoffTraceDefect M N (N - 40))
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M N (N - 40)))]
  exact ENNReal.ofReal_le_ofReal hfin

end ASDExplicitGamma.Native
