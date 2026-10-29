module

public import ASDExplicitGamma.Inverse.RawTraceSpatialAverage
public import ASDExplicitGamma.Inverse.RareSum
public import ASDExplicitGamma.Inverse.WeakHistoryIneq

/-! The raw-trace source interfaces, bundled in the common OLD law for
the parent-gap consumer. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

def rawParentGapTransportInput
    (M : ABKModel 2) (m : ℤ) (r : ℕ) (t : ℝ) : Prop :=
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
    (1 / 10^12 : ℝ) * theta M

def rawParentGapRareExpansionInput
    (M : ABKModel 2) (m : ℤ) (r : ℕ) (t : ℝ) : Prop :=
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
      (beta + R) ^ k * X = beta ^ k * X + rareExpansionTail beta R X k)

def rawParentGapWeakInput
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (s : Finset (TriadicCube 2))
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ))) : Prop :=
  let hShell := raw_trace_transport_shell_family_source
    M h hM hγ m r t ht hstate
  let Q := originCube 2 (m - (r : ℤ))
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let a : Cutoff.CutoffSample 2 → CoeffField 2 := fun ω =>
    (Model.partialInsertedCoefficient M m t ω).toFun
  let T : Cutoff.CutoffSample 2 → ℕ → ℝ := fun ω j =>
    rawWeakTraceSequence M m Q t ω j
  (∀ᵐ ω ∂μ,
    rawWeakTraceProxy
        (fun j => rawFiniteInverseDepthMax s (a ω)
          (Annealed.sigmaBar M m : ℝ) j)
        (T ω) ≤
      (1 + Scalar.inverseHistoryDiscount) *
        rawFiniteInverseHistoryMax s (a ω)
          (Annealed.sigmaBar M m : ℝ) * rawWeakTraceHistory (T ω)) ∧
  (‖rawWeakTraceHistoryLp M m Q t
      (rawWeakTraceSequenceMemLpFromShellTransport
        M h hγ m r hr t ht hstate hShell)‖ ≤
    (1 - Scalar.inverseHistoryDiscount) *
      ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
        rawWeakTraceProfileEnvelope M j)

/-! For a fixed root offset and insertion time, expose the three
conclusions needed by the remaining parent-gap argument. This adapter
adds no source premise beyond the native-state family and makes no claim about
the still-pending OLD source-energy slope. -/
theorem raw_parent_gap_source_inputs
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ))) :
    rawParentGapTransportInput M m r t ∧
      rawParentGapRareExpansionInput M m r t ∧
      rawParentGapWeakInput M h hM hγ m r hr t ht s hstate := by
  exact ⟨raw_trace_transport_profile_and_reserves_source
      M h hM hγ m r hr t ht hstate,
    ⟨raw_rare_sum_expansion_source
        M h hM hγ m r hr t ht hstate,
      raw_weak_trace_inequality_source
        M h hM hγ m r hr t ht s hs hstate⟩⟩

end ASDExplicitGamma.Inverse
