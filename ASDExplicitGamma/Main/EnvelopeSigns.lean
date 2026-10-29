module

public import ASDExplicitGamma.Main.EnvelopeRatios
import Mathlib.Tactic.FinCases

/-! Signs of the literal source envelopes, without estimated-slope premises. -/

@[expose] public section

namespace ASDExplicitGamma.Main

theorem mainKf_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ mainKf v := by
  unfold mainKf mainA2
  positivity

theorem mainJ0_nonneg {v gamma : ℝ} (hv : 0 ≤ v) (hg : 0 ≤ gamma) : 0 ≤ mainJ0 v gamma := by
  have hA := mainRawA_nonneg hg
  unfold mainJ0 mainRawFactor mainBetaOld
  positivity

theorem mainK0_nonneg {v gamma : ℝ} (hv : 0 ≤ v) (hg : 0 ≤ gamma) : 0 ≤ mainK0 v gamma := by
  have hA := mainRawA_nonneg hg
  unfold mainK0 mainRawFactor mainBetaOld
  positivity

theorem mainMu_nonneg {v gamma : ℝ} (hv : 0 ≤ v) (hg : 0 ≤ gamma) : 0 ≤ mainMu v gamma := by
  have hJ := mainJ0_nonneg hv hg
  have hK := mainK0_nonneg hv hg
  have hKf := mainKf_nonneg hv
  unfold mainMu mainBetaOld mainEpsOld
  positivity

theorem mainXiCoefficients_nonneg (v : ℝ) (i : Fin 3) : 0 ≤ mainXiCoefficients v i := by
  fin_cases i <;> norm_num [mainXiCoefficients, mainPa] <;> positivity

/-- The weighted-inverse slope is nonnegative throughout the source gamma
interval. Every geometric denominator is proved strictly positive. -/
theorem mainChi_nonneg {v gamma : ℝ} (hv : 0 ≤ v) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) :
    0 ≤ mainChi v gamma := by
  have hb : 0 ≤ mainBetaOld := by norm_num [mainBetaOld]
  have he : 0 ≤ mainEpsOld := by norm_num [mainEpsOld]
  have hf : 0 ≤ mainRawFactor gamma := by unfold mainRawFactor; positivity
  have hsum : 0 ≤ ∑ i : Fin 3, mainXiCoefficients v i *
      ((26/25)*mainBetaOld^3*mainRawFactor gamma*mainRawW gamma 10 (i.val+2)+
        52*v*Real.sqrt 3*mainBetaOld^4*mainW gamma 8 (i.val+2)) := by
    apply Finset.sum_nonneg
    intro i _
    have hc := mainXiCoefficients_nonneg v i
    have hr := mainRawW_nonneg hg0 hg (by norm_num : (10:ℝ) ≤ 10) (i.val+2)
    have hw := mainW_nonneg hg0 hg (by norm_num : (8:ℝ) ≤ 10) (i.val+2)
    positivity
  have hr := mainRawW_nonneg hg0 hg (by norm_num : (8:ℝ) ≤ 10) 2
  have hw := mainW_nonneg hg0 hg (by norm_num : (6:ℝ) ≤ 10) 2
  have hw4 := mainW_nonneg hg0 hg (by norm_num : (4:ℝ) ≤ 10) 0
  have hKf := mainKf_nonneg hv
  have hnum : 0 ≤ 1-mainAlpha^2 := by
    rw [mainAlpha_sq]
    exact (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))).le
  have hden : 0 < 1-mainAlpha^2*(3:ℝ)^(4*gamma+1/64) := by
    apply sub_pos.mpr
    exact main_weak_ratio_lt_one gamma _ hg (by linarith only [hg0])
  unfold mainChi
  positivity

/-- Nonnegative strong history is immediate from its literal square formula;
no derivative or transport inequality is assumed. -/
theorem mainEnvelopeH_nonneg (v gamma t : ℝ) : 0 ≤ mainEnvelopeH v gamma t := sq_nonneg _

theorem mainEnvelopeA_ge_initial {v gamma a0 t : ℝ} (hv : 0 ≤ v) (hg : 0 ≤ gamma) (ht : 0 ≤ t) :
    a0 ≤ mainEnvelopeA v gamma a0 t := by
  exact le_add_of_nonneg_right (mul_nonneg ht (mainMu_nonneg hv hg))

theorem mainEnvelopeXi_ge_initial {v gamma xiPre theta t : ℝ}
    (hv : 0 ≤ v) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (htheta : 0 ≤ theta) (ht : 0 ≤ t) :
    xiPre ≤ mainEnvelopeXi v gamma xiPre theta t := by
  unfold mainEnvelopeXi
  have hs := mainChi_nonneg hv hg0 hg
  have hr : 0 ≤ (1/10^12:ℝ)*theta := mul_nonneg (by norm_num) htheta
  have hprod := mul_nonneg ht hs
  linarith only [hr, hprod]

/-- Once the chosen source prefix constants clear the fixed support point,
the actual literal envelopes preserve both strict gates for all later times. -/
theorem mainEnvelope_support_gates {v gamma a0 xiPre theta t : ℝ}
    (hv : 0 ≤ v) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (htheta : 0 ≤ theta) (ht : 0 ≤ t)
    (ha0 : (1/100:ℝ) < a0) (hxi0 : mainBetaOld/100 < xiPre) :
    (1/100:ℝ) < mainEnvelopeA v gamma a0 t ∧
      mainBetaOld/100 < mainEnvelopeXi v gamma xiPre theta t := by
  exact ⟨ha0.trans_le (mainEnvelopeA_ge_initial hv hg0 ht),
    hxi0.trans_le (mainEnvelopeXi_ge_initial hv hg0 hg htheta ht)⟩

end ASDExplicitGamma.Main
