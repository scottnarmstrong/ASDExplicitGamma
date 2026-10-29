module

public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Native.OldSignedQ1WeakEnvelope
public import ASDExplicitGamma.Native.OldSignedActualJointMeanProxy

/-! Half of the explicit `mainEnvelopeXi` pays the actual directional
source-history budget of every depth-five cell: the leading half-trace term is
half of the local weighted mean row, and the doubled rare reserve fits the
`10^-12 theta` reserve of the envelope. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Numerics.Inverse
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Twice the complete discounted directional source-history budget of a
depth-five source cell is below the explicit `mainEnvelopeXi`. -/
theorem main_e_linear_source_history_half_xi_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) 5) :
    2 * ((1 - inverseHistoryDiscount ^ 2) *
      ∑' j : ℕ, inverseHistoryDiscount ^ (2 * j) *
        oldSignedSourceHistoryBudget M m U t j) ≤
      mainEnvelopeXi
        ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2)
        M.gamma (theta M * mainSourceInversePrefix) (theta M) t := by
  have hscale : U.scale = m - 5 := by
    have hh := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale = (originCube 2 m).scale - (5 : ℤ) at hh
    have hroot : (originCube 2 m).scale = m := rfl
    rw [hroot] at hh
    exact hh
  let α := inverseHistoryDiscount
  let d := 1 - α ^ 2
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  have hα := inverse_history_discount_range
  have hd : 0 ≤ d := sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)
  let R : ℕ → ℝ := fun j => α ^ (2 * j) *
    inverseBankDepthReserve .localInverse M j *
      (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j))
  have hR : Summable R := old_signed_depth_rare_summable M hγ
  have hbudgetSum : Summable (fun j : ℕ =>
      α ^ (2 * j) * oldSignedSourceHistoryBudget M m U t j) :=
    old_signed_source_history_budget_summable M h hM hγ m 5 le_rfl U hscale t
      ⟨ht.1, ht.2⟩ (fun l hl => hpast l (lt_of_le_of_lt hl hm))
  have htransport := mixed_bridge_local_mean_transport
    M h hM hγ N hpast m hm t ht
  have hterm (j : ℕ) :
      α ^ (2 * j) * oldSignedSourceHistoryBudget M m U t j =
        (1 / 2 : ℝ) * (α ^ (2 * j) * mixedBridgeOldInverseBaseline M j *
          inSourceMeanActual M m (5 + j) t) + R j := by
    unfold oldSignedSourceHistoryBudget
    rw [old_signed_q1_source_mean_eq M m U hscale t ⟨ht.1, ht.2⟩ j]
    norm_num only [inverseBankCap]
    unfold mixedBridgeOldInverseBaseline bankDepthFrame
    dsimp only [R, α]
    ring
  have hsum : (∑' j : ℕ, α ^ (2 * j) * oldSignedSourceHistoryBudget M m U t j) =
      (1 / 2 : ℝ) * (∑' j : ℕ, α ^ (2 * j) * mixedBridgeOldInverseBaseline M j *
          inSourceMeanActual M m (5 + j) t) + ∑' j, R j := by
    have hA : Summable (fun j : ℕ => α ^ (2 * j) *
        mixedBridgeOldInverseBaseline M j * inSourceMeanActual M m (5 + j) t) := by
      have h0 := htransport.1.mul_left (1 / (1 - α ^ 2))
      refine h0.congr (fun j => ?_)
      unfold mixedBridgeLocalWeight
      have : (1 - α ^ 2) ≠ 0 := by
        have : α ^ 2 < 1 := by nlinarith [hα.1, hα.2]
        linarith
      field_simp
      dsimp only [α]
      ring
    simp_rw [hterm]
    rw [(hA.mul_left (1 / 2 : ℝ)).tsum_add hR, tsum_mul_left]
  have hweighted : d * (∑' j : ℕ, α ^ (2 * j) *
      mixedBridgeOldInverseBaseline M j * inSourceMeanActual M m (5 + j) t) =
      ∑' j : ℕ, mixedBridgeLocalWeight M j * inSourceMeanActual M m (5 + j) t := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    unfold mixedBridgeLocalWeight
    dsimp only [d, α]
    ring
  have hrare := old_signed_directional_rare_delta M hγ
  have hR0 : 0 ≤ ∑' j, R j := tsum_nonneg (fun j => by
    dsimp only [R]
    apply mul_nonneg
    · exact mul_nonneg (pow_nonneg hα.1.le _)
        (by unfold inverseBankDepthReserve inverseBankReserve bankDepthFrame; positivity)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (ASDExplicitGamma.Cold.cold_theta_pos M).le
        (by rw [invTrace_coefficient.1]; positivity)) (sq_nonneg _))
        (Real.rpow_nonneg (by norm_num) _))
  have hrare2 : 2 * d * (∑' j, R j) ≤ (1 / 10 ^ 12 : ℝ) * theta M := by
    have h13 : 13 * d * (∑' j, R j) ≤ (1 / 10 ^ 12 : ℝ) * theta M := by
      simpa only [d, R, α] using hrare
    nlinarith [mul_nonneg hd hR0]
  have htheta0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  have htheta1 : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hxi0 : 0 ≤ (inSourceXi5Pre : ℝ) := by
    norm_num [inSourceXi5Pre,
      ASDExplicitGamma.Numerics.Native.nativeSource5Result]
  have hxiCapQ : inSourceXi5Pre ≤
      (140120486781 / 1000000000000 : ℚ) := by
    exact ASDExplicitGamma.Numerics.Native.nativeSource5_caps.2.2.1.le
  have hxiCap : (inSourceXi5Pre : ℝ) ≤
      (140120486781 / 1000000000000 : ℝ) := by
    have hxiCapR := (Rat.cast_le (K := ℝ)).2 hxiCapQ
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      Rat.cast_one] using hxiCapR
  have hprefixQ : (140120486781 / 1000000000000 : ℚ) ≤
      ASDExplicitGamma.Numerics.MainReturn.observer1Panel0Data.initialInverseMean - (1 / 10 ^ 12 : ℚ) := by
    decide +kernel
  have hprefix : (140120486781 / 1000000000000 : ℝ) ≤
      mainSourceInversePrefix := by
    change (140120486781 / 1000000000000 : ℝ) ≤
      (ASDExplicitGamma.Numerics.MainReturn.observer1Panel0Data.initialInverseMean : ℝ) - (1 / 10 ^ 12 : ℝ)
    have hprefixR := (Rat.cast_le (K := ℝ)).2 hprefixQ
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_one] using hprefixR
  have hpreCap : mixedXiPreCap M ≤ theta M * mainSourceInversePrefix := by
    rw [mixedXiPreCap]
    exact mul_le_mul_of_nonneg_left (hxiCap.trans hprefix) htheta0
  have hslope := mixed_bridge_local_slope_main_chi
    M h hM hγ N hpast m hm
  have htimeSlope : t * mixedBridgeLocalSlope M h m ≤
      t * mainChi v M.gamma :=
    mul_le_mul_of_nonneg_left hslope ht.1
  rw [hsum]
  calc
    2 * (d * ((1 / 2 : ℝ) * (∑' j : ℕ, α ^ (2 * j) *
        mixedBridgeOldInverseBaseline M j * inSourceMeanActual M m (5 + j) t) +
          ∑' j, R j)) =
      d * (∑' j : ℕ, α ^ (2 * j) * mixedBridgeOldInverseBaseline M j *
        inSourceMeanActual M m (5 + j) t) + 2 * d * (∑' j, R j) := by ring
    _ ≤ (mixedXiPreCap M + t * mixedBridgeLocalSlope M h m) +
        (1 / 10 ^ 12 : ℝ) * theta M := by
      rw [hweighted]
      exact add_le_add htransport.2 hrare2
    _ ≤ theta M * mainSourceInversePrefix + (1 / 10 ^ 12 : ℝ) * theta M +
        t * mainChi v M.gamma := by linarith
    _ = _ := rfl

end ASDExplicitGamma.Main
