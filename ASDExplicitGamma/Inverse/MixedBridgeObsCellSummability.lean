module

public import ASDExplicitGamma.Inverse.MixedBridgeObsCellTrace
public import ASDExplicitGamma.Inverse.WeakHistoryIneq

/-! Almost-everywhere summability of translated local OLD trace rows. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse
open ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem mixed_bridge_obscell_profile_nonneg
    (M : ABKModel 2) (j : ℕ) :
    0 ≤ rawWeakTraceProfileEnvelope M j := by
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  unfold rawWeakTraceProfileEnvelope
  positivity

private theorem mixed_bridge_obscell_profile_weighted_summable
    (M : ABKModel 2) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      rawWeakTraceProfileEnvelope M j) := by
  let α : ℝ := Scalar.inverseHistoryDiscount
  let q : ℝ := α * (3 : ℝ) ^ (6 * gammaZero)
  have hqeq : q = (3 : ℝ) ^ (6 * gammaZero - 1 / 4) := by
    dsimp [q, α, Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hq0 : 0 ≤ q := by rw [hqeq]; positivity
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
  have hterm (j : ℕ) :
      Scalar.inverseHistoryDiscount ^ j * rawWeakTraceProfileEnvelope M j =
        (theta M * (invTraceM : ℚ)) *
          ((1 + (j : ℝ)) ^ 2 * q ^ j) := by
    rw [rawWeakTraceProfileEnvelope, hpow]
    dsimp [q]
    ring
  have hpoly' := hpoly.mul_left (theta M * (invTraceM : ℚ))
  exact hpoly'.congr fun j => (hterm j).symm

/-- The translated depth-five trace sequence has the same weighted a.e.
summability as the root sequence. The proof uses its actual-law L² profile
and positivity; no independence or translated global-bank assertion enters. -/
theorem mixed_bridge_obscell_trace_weighted_summable_ae
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hU : U.scale = m - ((5 : ℕ) : ℤ)) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
        mixedDepthTraceAverage M m U t ω j) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => mixedDepthTraceAverage M m U t ω j
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ :=
    fun j ω => α ^ j * T j ω
  have hα := Scalar.inverse_history_discount_range
  have hprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
    simpa [T, μ] using
      mixed_bridge_obscell_trace_profile M h hM hγ N hpast m hm t ht
        5 (by omega) U hU j
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    have hne : eLpNorm (T j) 2 μ < ⊤ :=
      (hprofile j).trans_lt ENNReal.ofReal_lt_top
    exact (memLp_iff).mpr hne
  have hFmem (j : ℕ) : MemLp (F j) 2 μ := by
    change MemLp ((α ^ j) • T j) 2 μ
    exact (hTmem j).const_smul (α ^ j)
  have hprofileSummable : Summable (fun j : ℕ =>
      α ^ j * rawWeakTraceProfileEnvelope M j) := by
    simpa [α] using mixed_bridge_obscell_profile_weighted_summable M
  have hFbound (j : ℕ) : lpNorm (F j) 2 μ ≤
      α ^ j * rawWeakTraceProfileEnvelope M j := by
    have hαj : 0 ≤ α ^ j := pow_nonneg hα.1.le j
    have hCj : 0 ≤ rawWeakTraceProfileEnvelope M j :=
      mixed_bridge_obscell_profile_nonneg M j
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
          mul_le_mul_of_nonneg_left (hprofile j) (by positivity)
        _ = ENNReal.ofReal
            (α ^ j * rawWeakTraceProfileEnvelope M j) :=
          (ENNReal.ofReal_mul hαj).symm
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hscaled
    rw [ENNReal.toReal_ofReal (mul_nonneg hαj hCj)] at hreal
    rw [← toReal_eLpNorm]
    exact hreal
  have hnormSummable : Summable (fun j : ℕ => lpNorm (F j) 2 μ) :=
    Summable.of_nonneg_of_le (fun j => lpNorm_nonneg) hFbound
      hprofileSummable
  have hnormSumFinite : (∑' j : ℕ, eLpNorm (F j) 2 μ) ≠ ⊤ := by
    have hsumEq : (∑' j : ℕ, eLpNorm (F j) 2 μ) =
        ∑' j : ℕ, ENNReal.ofReal (lpNorm (F j) 2 μ) := by
      apply tsum_congr
      intro j
      exact (ofReal_lpNorm (hFmem j)).symm
    rw [hsumEq]
    exact ne_of_lt hnormSummable.tsum_ofReal_lt_top
  have hpoint := summable_norm_of_tsum_eLpNorm_ne_top
    (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) hnormSumFinite
  have hTnonneg (ω : Cutoff.CutoffSample 2) (j : ℕ) : 0 ≤ T j ω := by
    simpa [T, mixedDepthTraceAverage] using
      raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j
  filter_upwards [hpoint] with ω hω
  apply hω.congr
  intro j
  change |α ^ j * T j ω| = α ^ j * T j ω
  exact abs_of_nonneg (mul_nonneg (pow_nonneg hα.1.le j) (hTnonneg ω j))

end
end ASDExplicitGamma.Inverse
