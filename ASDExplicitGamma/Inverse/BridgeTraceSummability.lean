module

public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Inverse.WeakHistoryIneq

/-! The actual mixed-bridge trace history is pointwise summable from the
shell output. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Scalar
open scoped ENNReal

noncomputable section

theorem mixed_bridge_raw_trace_weighted_summable_ae
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ))) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
        mixedBridgeTbar M m t ω j) := by
  let Q := originCube 2 m
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    rawWeakTraceSequence M m Q t ω j
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => α ^ j * T j ω
  have hstate0 : ∀ j : ℕ,
      nativeInductionState M h (m - (0 : ℤ) - (j : ℤ)) := by
    intro j
    simpa using hstate j
  let hShell := raw_trace_transport_shell_family_source
    M h hM hγ m 0 t ht hstate0
  let hT := rawWeakTraceSequenceMemLpFromShellTransport
    M h hγ m 0 (by omega) t ht hstate0 hShell
  have hα := Scalar.inverse_history_discount_range
  let q : ℝ := α * (3 : ℝ) ^ (6 * gammaZero)
  have hqeq : q = (3 : ℝ) ^ (6 * gammaZero - 1 / 4) := by
    dsimp [q, α, Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hq0 : 0 ≤ q := by
    rw [hqeq]
    positivity
  have hq1 : q < 1 := by
    rw [hqeq]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
    norm_num [gammaZero]
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hlin : Summable (fun j : ℕ => (j : ℝ) * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm
  have hquad : Summable (fun j : ℕ => (j : ℝ) ^ 2 * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 2 hqnorm
  have hpoly : Summable (fun j : ℕ => (1 + (j : ℝ)) ^ 2 * q ^ j) := by
    have hsum := hquad.add (hlin.mul_left 2)
    have hsum' := hsum.add hgeom
    apply hsum'.congr
    intro j
    ring
  have hpow (j : ℕ) :
      (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) =
        ((3 : ℝ) ^ (6 * gammaZero)) ^ j := by
    rw [show 6 * gammaZero * (j : ℝ) =
      (6 * gammaZero) * (j : ℝ) by ring]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (6 * gammaZero)) j]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hU : Summable (fun j : ℕ => α ^ j *
      rawWeakTraceProfileEnvelope M j) := by
    have hterm (j : ℕ) : α ^ j * rawWeakTraceProfileEnvelope M j =
        (theta M * (invTraceM : ℚ)) * ((1 + (j : ℝ)) ^ 2 * q ^ j) := by
      rw [rawWeakTraceProfileEnvelope, hpow]
      dsimp [q]
      ring
    have hscaled := hpoly.mul_left (theta M * (invTraceM : ℚ))
    exact hscaled.congr fun j => (hterm j).symm
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m 0 (by omega) t ht hstate0 hShell
  have hFmem (j : ℕ) : MemLp (F j) 2 μ := by
    have hTj : MemLp (T j) 2 μ := by
      simpa [T, Q, μ] using hT j
    change MemLp ((α ^ j) • T j) 2 μ
    exact hTj.const_smul (α ^ j)
  have hFbound (j : ℕ) : lpNorm (F j) 2 μ ≤
      α ^ j * rawWeakTraceProfileEnvelope M j := by
    have hUj : 0 ≤ rawWeakTraceProfileEnvelope M j := by
      unfold rawWeakTraceProfileEnvelope
      have ht0 : 0 ≤ theta M := by
        unfold theta
        exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
      have hMrat : 0 ≤ invTraceM := by
        rw [invTrace_coefficient.1]
        positivity
      have hM0 : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
      positivity
    have hαj : 0 ≤ α ^ j := pow_nonneg hα.1.le j
    have hprofilej : eLpNorm (T j) 2 μ ≤
        ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
      simpa [T, Q, rawWeakTraceProfileEnvelope] using hprofile j
    have hscaled : eLpNorm (F j) 2 μ ≤
        ENNReal.ofReal (α ^ j * rawWeakTraceProfileEnvelope M j) := by
      have hFfun : F j = (α ^ j) • T j := by
        funext ω
        rfl
      calc
        eLpNorm (F j) 2 μ =
            ENNReal.ofReal (α ^ j) * eLpNorm (T j) 2 μ := by
          rw [hFfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hαj]
        _ ≤ ENNReal.ofReal (α ^ j) *
            ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) :=
          mul_le_mul_of_nonneg_left hprofilej (by positivity)
        _ = ENNReal.ofReal (α ^ j * rawWeakTraceProfileEnvelope M j) :=
          (ENNReal.ofReal_mul hαj).symm
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hscaled
    rw [ENNReal.toReal_ofReal (mul_nonneg hαj hUj)] at hreal
    rw [← toReal_eLpNorm]
    exact hreal
  have hnormSummable : Summable (fun j : ℕ => lpNorm (F j) 2 μ) :=
    Summable.of_nonneg_of_le (fun j => lpNorm_nonneg) hFbound hU
  have hnormSumFinite : (∑' j : ℕ, eLpNorm (F j) 2 μ) ≠ ∞ := by
    have hsumEq : (∑' j : ℕ, eLpNorm (F j) 2 μ) =
        ∑' j : ℕ, ENNReal.ofReal (lpNorm (F j) 2 μ) := by
      apply tsum_congr
      intro j
      exact (ofReal_lpNorm (hFmem j)).symm
    rw [hsumEq]
    exact ne_of_lt hnormSummable.tsum_ofReal_lt_top
  have hpoint := summable_norm_of_tsum_eLpNorm_ne_top
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hnormSumFinite
  have hTnonneg (ω : Cutoff.CutoffSample 2) (j : ℕ) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  filter_upwards [hpoint] with ω hω
  apply hω.congr
  intro j
  change |α ^ j * T j ω| = α ^ j * T j ω
  have hαj : 0 ≤ α ^ j := pow_nonneg hα.1.le j
  exact abs_of_nonneg (mul_nonneg hαj (hTnonneg ω j))

end
end ASDExplicitGamma.Inverse
