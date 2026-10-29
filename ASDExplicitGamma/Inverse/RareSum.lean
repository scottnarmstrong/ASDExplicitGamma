module

public import ASDExplicitGamma.Inverse.RawRareExpansion
public import ASDExplicitGamma.Inverse.RawTraceSpatialAverage
public import ASDExplicitGamma.Inverse.RawTraceTransport

/-! The source-order rare expansion paired with the shell-derived raw-trace
profile and its two audited reserve budgets. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable section

/-- The trace profile and reserve bounds, together with the exact
order-zero-through-three rare-factor expansion. The only theorem-shaped
input is the exact finite-band p=20 conclusion at each source depth. -/
theorem raw_rare_sum_expansion_of_shell_transport_helper
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField
              (closure (cubeSet (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal
          (rawTraceBandShellIncrement M.gamma (134 + j))) :
    (∀ j : ℕ,
      eLpNorm (rawTraceTransportBandObservable M m r t j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j))) ∧
    (∀ j : ℕ,
      eLpNorm
        (fun ω => rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j))) ∧
    (5400 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta M ≤
        (1 / 10^12 : ℝ) * theta M ∧
    (27000 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta M ≤
        (1 / 10^12 : ℝ) * theta M ∧
    (∀ (beta R X : ℝ) (k : ℕ), k ≤ 3 →
      (beta + R) ^ k * X = beta ^ k * X + rareExpansionTail beta R X k) := by
  have hprofile := raw_trace_transport_origin_depth_family_helper
    M h hγ m r hr t ht hstate hShell
  have haverage := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m r hr t ht hstate hShell
  have htheta0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hreserve := raw_trace_transport_rare_reserves_helper (theta M) htheta0
  refine ⟨hprofile, haverage, hreserve.1, hreserve.2, ?_⟩
  intro beta R X k hk
  exact rare_expansion_binomial beta R X k hk

/-- IN-RARE-SUM-EXPANSION. The per-depth p=20 inputs are
instantiated from the exact theorem and the native-state family; the actual
trace profiles, reserve bounds, and order-three rare-factor expansion follow
without a shell-transport premise. -/
theorem raw_rare_sum_expansion_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ))) :
    (∀ j : ℕ,
      eLpNorm (rawTraceTransportBandObservable M m r t j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j))) ∧
    (∀ j : ℕ,
      eLpNorm
        (fun ω => rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j))) ∧
    (5400 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta M ≤
        (1 / 10^12 : ℝ) * theta M ∧
    (27000 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta M ≤
        (1 / 10^12 : ℝ) * theta M ∧
    (∀ (beta R X : ℝ) (k : ℕ), k ≤ 3 →
      (beta + R) ^ k * X = beta ^ k * X + rareExpansionTail beta R X k) := by
  exact raw_rare_sum_expansion_of_shell_transport_helper
    M h hγ m r hr t ht hstate
    (raw_trace_transport_shell_family_source
      M h hM hγ m r t ht hstate)

end
end ASDExplicitGamma.Inverse
