/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.Profile
public import ASDExplicitGamma.Main.PartialInsertion

/-! # The reset profile on a single actual shell insertion path -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- The deterministic shell weights for the actual heat path: all completed
shells have unit weight and the active shell has amplitude `sqrt t`. -/
noncomputable def aoCirStepWeights (N : ℤ) (t : ℝ) (k : ℤ) : ℝ :=
  if k < N then 1 else if k = N then Real.sqrt t else 0

theorem aoCirStepWeights_bounds {N : ℤ} {t : ℝ}
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℤ) :
    0 ≤ aoCirStepWeights N t k ∧ aoCirStepWeights N t k ≤ 1 := by
  unfold aoCirStepWeights
  split_ifs with hlt heq
  · norm_num
  · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr ht1⟩
  · norm_num

/-- The reset's finite attenuated coefficient is the actual one-shell model
path, based at the preceding completed cutoff. -/
theorem aoCir_step_coefficient (M : ABKModel 2) (base N : ℤ)
    (hbase : base < N) (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    attenuatedCoefficient M base N (aoCirStepWeights N t) ω x =
      Model.partialInsertedCoefficient M (N - 1) t ω x := by
  classical
  have hterm (k : ℤ) :
      aoCirStepWeights N t k • (ω.val k).forgetShell x =
        (if k < N then (ω.val k).forgetShell x else 0) +
          (if k = N then Real.sqrt t • (ω.val k).forgetShell x else 0) := by
    by_cases hlt : k < N
    · simp [aoCirStepWeights, hlt, ne_of_lt hlt]
    · by_cases heq : k = N
      · simp [aoCirStepWeights, heq]
      · simp [aoCirStepWeights, hlt, heq]
  have hsets : (Finset.Ioc base N).filter (fun k => k < N) =
      Finset.Ioc base (N - 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hfirst :
      (∑ k ∈ Finset.Ioc base N,
        if k < N then (ω.val k).forgetShell x else 0) =
        ∑ k ∈ Finset.Ioc base (N - 1), (ω.val k).forgetShell x := by
    rw [← Finset.sum_filter, hsets]
  have hmem : N ∈ Finset.Ioc base N := by
    simp only [Finset.mem_Ioc]
    omega
  have hsum :
      (∑ k ∈ Finset.Ioc base N,
        aoCirStepWeights N t k • (ω.val k).forgetShell x) =
        (∑ k ∈ Finset.Ioc base (N - 1), (ω.val k).forgetShell x) +
          Real.sqrt t • (ω.val N).forgetShell x := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, hfirst]
    simp only [Finset.sum_ite_eq', hmem, ite_true]
  have hc := congrArg (fun a : RegCoeffField 2 => a x)
    (Cutoff.cutoff_add_finiteShellIncrement ω
      (show base ≤ N - 1 by omega))
  change Cutoff.cutoff base ω x + Cutoff.finiteShellIncrement ω.val base (N - 1) x =
    Cutoff.cutoff (N - 1) ω x at hc
  rw [Cutoff.finiteShellIncrement_apply] at hc
  change Cutoff.cutoff base ω x +
      (∑ k ∈ Finset.Ioc base (N - 1), (ω.val k).forgetShell x) =
    Cutoff.cutoff (N - 1) ω x at hc
  have hpi : Model.partialInsertedCoefficient M (N - 1) t ω x =
      Cutoff.coefficientCutoff M.nu (N - 1) ω x +
        Real.sqrt t • (ω.val N).forgetShell x := by
    have h := congrArg (fun a : RegCoeffField 2 => a x)
      (Main.mainInsertion_coefficient M (N - 1) t ω)
    simpa [RegCoeffField.add_apply, RegCoeffField.smul_apply] using h
  unfold attenuatedCoefficient
  rw [hsum, hpi, Cutoff.coefficientCutoff_apply,
    Cutoff.coefficientCutoff_apply, ← hc]
  abel

/-- Apply the one permitted reset producer to an actual partial shell path.
The reset's native-past premise is discharged from the all-label native state;
the profile remains in the requested fixed true frame `K₀`. -/
theorem aoCir_step_profile_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ n : ℤ, nativeInductionState M h n)
    (Q : TriadicCube 2) (N K₀ : ℤ) (hQN : Q.scale ≤ N)
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    orderResetProfileConclusion M Q p N K₀ (aoCirStepWeights N t) := by
  have hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * orderBand p → nativeInductionState M h n := by
    intro n _
    exact hstate n
  have hN : Q.scale - 1 ≤ N := by omega
  have hw : ∀ k ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ aoCirStepWeights N t k ∧ aoCirStepWeights N t k ≤ 1 := by
    intro k hk
    exact aoCirStepWeights_bounds ht0 ht1 k
  exact ao_all_profile_of_order_reset reset M h hM hγ Q p hp hpast
    N K₀ hN (aoCirStepWeights N t) hw

/-- The exact native-band caps on an actual one-shell path, extracted from
the source reset profiles.  The trace and inverse exponents may differ, as in
the `2p`/`4p` Hölder orders used by the finite-even recurrence. -/
theorem aoCir_step_small_gamma_profile_caps_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ n : ℤ, nativeInductionState M h n)
    (Q_T Q_I : TriadicCube 2) (N : ℤ)
    (hQTN : Q_T.scale ≤ N) (hNhi : N ≤ Q_T.scale + 8)
    (hQIN : Q_I.scale ≤ N) (K_T K_I : ℤ)
    (hfT : |((K_T - Q_T.scale + 1 : ℤ) : ℝ)| ≤ 1)
    (hfI : |((K_I - Q_I.scale + 1 : ℤ) : ℝ)| ≤ 5)
    (qT qI : ℝ)
    (hqT : 2 ≤ qT) (hqTband : qT ≤ 4 * (smallGammaSeedP M.gamma : ℝ))
    (hqI : 48 ≤ qI) (hqIband : qI ≤ 4 * (smallGammaSeedP M.gamma : ℝ))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (Inverse.rootTraceObservable M Q_T
      (Inverse.protectedOldLabel Q_T.scale (Inverse.orderBand qT))
      N K_T (aoCirStepWeights N t)) (ENNReal.ofReal qT)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal 50 ∧
    aoCirInverseHistoryFactor M.gamma * (3 : ℝ) ^ (8 / qI) *
      (eLpNorm (Inverse.rootInverseObservable M Q_I
        (Inverse.protectedOldLabel Q_I.scale (Inverse.orderBand qI))
        N K_I (aoCirStepWeights N t)) (ENNReal.ofReal qI)
          (Cutoff.cutoffSampleLaw M).toMeasure).toReal < 2.2 := by
  have hprofT := aoCir_step_profile_of_reset reset M h hM hγ hstate Q_T N K_T hQTN qT hqT t ht0 ht1
  have hprofI := aoCir_step_profile_of_reset reset M h hM hγ hstate Q_I N K_I hQIN qI
    (by linarith [hqI]) t ht0 ht1
  let D : ℝ := ((N - Q_T.scale + 1 : ℤ) : ℝ)
  let fT : ℝ := |((K_T - Q_T.scale + 1 : ℤ) : ℝ)|
  let fI : ℝ := |((K_I - Q_I.scale + 1 : ℤ) : ℝ)|
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact_mod_cast (show 0 ≤ N - Q_T.scale + 1 by omega)
  have hD : D ≤ 9 := by
    dsimp [D]
    exact_mod_cast (show N - Q_T.scale + 1 ≤ 9 by omega)
  have hfT0 : 0 ≤ fT := abs_nonneg _
  have hfI0 : 0 ≤ fI := abs_nonneg _
  have htrace : eLpNorm (Inverse.rootTraceObservable M Q_T
      (Inverse.protectedOldLabel Q_T.scale (Inverse.orderBand qT))
      N K_T (aoCirStepWeights N t)) (ENNReal.ofReal qT)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Inverse.orderTraceProfile M.gamma qT D fT) := by
    simpa only [orderResetProfileConclusion, D, fT] using hprofT.1
  have hinverse : eLpNorm (Inverse.rootInverseObservable M Q_I
      (Inverse.protectedOldLabel Q_I.scale (Inverse.orderBand qI))
      N K_I (aoCirStepWeights N t)) (ENNReal.ofReal qI)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Inverse.orderInverseProfile (153 / 100) M.gamma qI fI) := by
    have hi := hprofI.2.2 hγsmall
    simpa only [orderResetProfileConclusion, D, fI] using hi
  exact aoCir_small_gamma_caps_of_all_profile M.shellPrefix.gamma_pos hγsmall
    hqT hqTband hqI hqIband hD0 hD hfT0 hfT hfI0 hfI
    htrace hinverse

end ASDExplicitGamma.AllOrder
