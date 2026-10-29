module

public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPointwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPathwise
public import ASDExplicitGamma.Main.HotFeedbackBill
public import ASDExplicitGamma.Main.ThetaGeneratorHotESourceSquareNode
public import ASDExplicitGamma.Main.ELinearKappa
public import ASDExplicitGamma.Main.ELinearCauchy
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellEnergy

/-! Node MA-E-REMAINDER-FEEDBACK, pathwise step: the feedback group of the hot trial at the
observer root is at most `2 k_d (63/50) B* (sqrt 2 d' + G d')`, with `d'` the RMS hot source size
and `G` the RMS parent reciprocal error. The inverse history is the NEW global variable `B*`
only through the cell histories `B_U <= B*`; no OLD proxy is replaced. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- The `R'` feedback group of the hot trial as a function of the cutoff sample
(the `2 * feedbackSource` series of `mainETermResidualFeedbackFamily`). -/
def mainHotFeedbackRow_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ∑' n : whiteBasisIndex, (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (hotRootCoefficient_Th m hobs t ω) b (q3ModelLength (m + 1))).feedbackSource n

/-- RMS size `d'` of the hot source over the observer cells. -/
def mainHotSourceRms_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
    hotSourceSize (fun n P x => hotPatchSource (originCube 2 (m + hobs)) (hobs + 5)
      (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (hotRootCoefficient_Th m hobs t ω) b
      (q3ModelLength (m + 1)) n P x) U ^ 2))

/-- RMS parent reciprocal error over the observer cells. -/
def mainHotReciprocalRms_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
    oldSignedReciprocalErrorSize (originCube 2 (m + hobs)) U M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1 (hotRootCoefficient_Th m hobs t ω) ^ 2))

theorem mainHotSourceRms_nonneg_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t b : ℝ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ mainHotSourceRms_Th M m hobs t b ω :=
  Real.sqrt_nonneg _

theorem main_hot_feedback_row_le_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) (ω : Cutoff.CutoffSample 2) :
    mainHotFeedbackRow_Th M m hobs t b ω ≤
      2 * mainKd (b ^ 2) * (63 / 50) *
        (Real.sqrt 2 * (mixedBridgeBstar M m t ω * mainHotSourceRms_Th M m hobs t b ω) +
          mixedBridgeBstar M m t ω * mainHotReciprocalRms_Th M m hobs t ω *
            mainHotSourceRms_Th M m hobs t b ω) := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  let Q := originCube 2 (m + hobs)
  let S := descendantsAtDepth Q (hobs + 5)
  let Bs := mixedBridgeBstar M m t ω
  let L := q3ModelLength (m + 1)
  let k := hotRootCoefficient_Th m hobs t ω
  let sU : TriadicCube 2 → ℝ := fun U => hotSourceSize (fun n P x =>
    hotPatchSource Q (hobs + 5) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k b L
      n P x) U
  let GU : TriadicCube 2 → ℝ := fun U => oldSignedReciprocalErrorSize Q U M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k
  let kd := mainKd (b ^ 2)
  have hBs : 0 ≤ Bs := mixed_bridge_bstar_nonneg M m t ω
  have hkd : 0 ≤ kd := mainKd_nonneg _
  have hbill := (hot_source_feedback_bill (m + hobs) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos hσ k b L (hot_cells_scale_Th m hobs)).2
  have hα := inverseHistoryDiscount_le
  have hα0 := inverse_history_discount_range.1
  have hL := hot_cells_scale_Th m hobs
  have h36 : (3 : ℝ) ^ (-6 : ℤ) * 3 ^ 6 = 1 := by norm_num
  have hcell : descendantsAverage Q (hobs + 5) (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
        (Real.sqrt 2 + oldSignedReciprocalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos hσ k) *
        ((1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) k) * sU U)) ≤
      descendantsAverage Q (hobs + 5) (fun U =>
        (kd * (63 / 50) * Bs) * (Real.sqrt 2 * sU U + GU U * sU U)) := by
    refine descendantsAverage_le fun U hU => ?_
    have hκ : oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 ≤ kd := by
      apply old_signed_derivative_kappa_le_mainKd _ _ _ (Triadic.cubeScaleFactor_pos' U).le
      have := hL U hU
      have e : cubeScaleFactor U = (3 : ℝ) ^ (-6 : ℤ) * (cubeScaleFactor U * 3 ^ 6) := by
        rw [mul_comm (cubeScaleFactor U), ← mul_assoc, h36, one_mul]
      rw [e]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hκ0 : 0 ≤ oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 :=
      old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
    have hH : oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) k) ≤ Bs :=
      hot_cell_history_le_bstar M m hobs h40 t ht ω U hU
    have hH0 : 0 ≤ oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) k) :=
      lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))
    have hs0 : 0 ≤ sU U := Real.sqrt_nonneg _
    have hG0 : 0 ≤ GU U := Real.sqrt_nonneg _
    have hc : (1 / 2 + inverseHistoryDiscount) ≤ 63 / 50 := by linarith
    have hc0 : 0 ≤ 1 / 2 + inverseHistoryDiscount := by linarith
    have h2 : 0 ≤ Real.sqrt 2 + GU U := add_nonneg (Real.sqrt_nonneg _) hG0
    have h3 : (1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ) k) * sU U ≤
        (63 / 50) * Bs * sU U :=
      mul_le_mul_of_nonneg_right (mul_le_mul hc hH hH0 (by norm_num)) hs0
    have h4 := mul_le_mul_of_nonneg_left h3 h2
    have h5 := mul_le_mul hκ h4 (mul_nonneg h2 (mul_nonneg (mul_nonneg hc0 hH0) hs0)) hkd
    refine le_trans (le_of_eq (mul_assoc _ _ _)) (h5.trans (le_of_eq ?_))
    show kd * ((Real.sqrt 2 + GU U) * ((63 / 50) * Bs * sU U)) = _
    ring
  have hlin : descendantsAverage Q (hobs + 5) (fun U =>
      (kd * (63 / 50) * Bs) * (Real.sqrt 2 * sU U + GU U * sU U)) ≤
      kd * (63 / 50) * Bs * (Real.sqrt 2 * mainHotSourceRms_Th M m hobs t b ω +
        mainHotReciprocalRms_Th M m hobs t ω * mainHotSourceRms_Th M m hobs t b ω) := by
    rw [hot_desc_average_const_mul_Th]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsplit : descendantsAverage Q (hobs + 5) (fun U => Real.sqrt 2 * sU U + GU U * sU U) =
        Real.sqrt 2 * descendantsAverage Q (hobs + 5) sU +
          descendantsAverage Q (hobs + 5) (fun U => GU U * sU U) := by
      show finAvg S _ = Real.sqrt 2 * finAvg S sU + finAvg S _
      rw [finAvg_add, finAvg_mul_left]
    rw [hsplit]
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_left (finAvg_le_sqrt S sU) (Real.sqrt_nonneg _)
    · exact finAvg_mul_le S GU sU
  have habs : mainHotFeedbackRow_Th M m hobs t b ω ≤ 2 * |∑' n : whiteBasisIndex,
      (hotPatchTrialTerms Q (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k b L
        ).feedbackSource n| := by
    unfold mainHotFeedbackRow_Th
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  have htot : mainHotFeedbackRow_Th M m hobs t b ω ≤
      2 * (kd * (63 / 50) * Bs * (Real.sqrt 2 * mainHotSourceRms_Th M m hobs t b ω +
        mainHotReciprocalRms_Th M m hobs t ω * mainHotSourceRms_Th M m hobs t b ω)) :=
    habs.trans (mul_le_mul_of_nonneg_left (hbill.trans (hcell.trans hlin)) (by norm_num))
  refine htot.trans (le_of_eq ?_)
  ring

end

end ASDExplicitGamma.Main
