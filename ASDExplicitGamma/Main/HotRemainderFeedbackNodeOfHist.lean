module

public import ASDExplicitGamma.Main.HotRemainderFeedbackNode
public import ASDExplicitGamma.Main.HotObsSplitOfHist

/-! Successors of `HotRemainderFeedbackNode` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- Successor of `main_hot_e_remainder_feedback` with the history envelope `Hfun`. -/
theorem main_hot_e_remainder_feedback_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := Hfun t
    (∫ ω, mainHotFeedbackRow M m hobs t b ω ∂μ) ≤
      2 * mainKd (b ^ 2) * (63 / 50) *
        (Real.sqrt 2 * mainBeta * mainLoadD (b ^ 2) a f H xi (mainKd (b ^ 2)) +
          mainLoadZ (b ^ 2) a f H xi (mainKd (b ^ 2)) * mainRec xi) := by
  classical
  intro μ v xi a f H
  let Q := originCube 2 (m + hobs)
  let Bs : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let Dr : Cutoff.CutoffSample 2 → ℝ := mainHotDropObs M m hobs t
  let V2 : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    descendantsAverage Q (hobs + 5) (fun U => mixedBridgeVLocal M m U t ω ^ 2)
  let Th : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    descendantsAverage Q (hobs + 5) (fun U => mixedOldTheta M m U t ω)
  let ka := mainKa (b ^ 2)
  let kd := mainKd (b ^ 2)
  let Dm : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ka * Real.sqrt (Bs ω * Dr ω) + kd * Real.sqrt (V2 ω)
  let Gt : Cutoff.CutoffSample 2 → ℝ := fun ω => Real.sqrt (2 * Th ω)
  have hbs : mixedGlobalHistoryMax M m t = Bs :=
    funext fun ω => main_hot_bstar_eq M m t ht ω
  have hsplit := main_hot_obs_positive_split_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs t ht
  rw [hbs] at hsplit
  have hBs0 : ∀ ω, 0 ≤ Bs ω := fun ω => mixed_bridge_bstar_nonneg M m t ω
  have hDr0 : ∀ ω, 0 ≤ Dr ω := fun ω => (main_hot_drop_obs_pathwise M m hobs t ω).2
  have hV20 : ∀ ω, 0 ≤ V2 ω := fun ω => by
    show 0 ≤ ((descendantsAtDepth Q (hobs + 5)).card : ℝ)⁻¹ *
      ∑ U ∈ descendantsAtDepth Q (hobs + 5), mixedBridgeVLocal M m U t ω ^ 2
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun U _ => sq_nonneg _)
  have hTh0 : ∀ ω, 0 ≤ Th ω := fun ω => hot_reciprocal_theta_nonneg M hγ m hobs h40 t ht ω
  have hka : 0 ≤ ka := by unfold ka mainKa mainA2; positivity
  have hkd : 0 ≤ kd := mainKd_nonneg _
  have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hDm0 : ∀ ω, 0 ≤ Dm ω := fun ω =>
    add_nonneg (mul_nonneg hka (Real.sqrt_nonneg _)) (mul_nonneg hkd (Real.sqrt_nonneg _))
  have hGt0 : ∀ ω, 0 ≤ Gt ω := fun ω => Real.sqrt_nonneg _
  obtain ⟨hBint, hEB, hB2int, hEB2⟩ := hot_bstar_moments M h hM hγ N hpast m hm t ht
  obtain ⟨hBVint, hBVle⟩ := hot_obs_bv2_sharp M h hM hγ N hpast m hm hobs h40 t ht
  obtain ⟨hBTint, hBTle⟩ := hot_obs_avg_theta_weighted M h hM hγ N hpast m hm hobs t ht
  -- (1a) E[B sqrt(B Δ)] ≤ β R1
  have hCa := main_cauchy_sqrt_expectation μ (fun ω => Bs ω ^ 2) (fun ω => Bs ω * Dr ω)
    hB2int hsplit.1 (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hBs0 ω) (hDr0 ω))
  have eA : (fun ω => Real.sqrt (Bs ω ^ 2) * Real.sqrt (Bs ω * Dr ω)) =
      fun ω => Bs ω * Real.sqrt (Bs ω * Dr ω) := by
    funext ω
    rw [Real.sqrt_sq (hBs0 ω)]
  rw [eA] at hCa
  have hAle : (∫ ω, Bs ω * Real.sqrt (Bs ω * Dr ω) ∂μ) ≤ mainBeta * mainR1 a f H := by
    refine hCa.2.trans ?_
    unfold mainR1 mainHd
    exact mul_le_mul ((Real.sqrt_le_sqrt hEB2).trans_eq (Real.sqrt_sq hβ))
      (Real.sqrt_le_sqrt hsplit.2.1) (Real.sqrt_nonneg _) hβ
  -- (1b) E[B sqrt(V2)] ≤ β sqrt ξ
  have hCb := main_cauchy_sqrt_expectation μ Bs (fun ω => Bs ω * V2 ω)
    hBint hBVint (Filter.Eventually.of_forall hBs0)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hBs0 ω) (hV20 ω))
  have eB : (fun ω => Real.sqrt (Bs ω) * Real.sqrt (Bs ω * V2 ω)) =
      fun ω => Bs ω * Real.sqrt (V2 ω) := by
    funext ω
    rw [Real.sqrt_mul (hBs0 ω), ← mul_assoc, Real.mul_self_sqrt (hBs0 ω)]
  rw [eB] at hCb
  have hBle : (∫ ω, Bs ω * Real.sqrt (V2 ω) ∂μ) ≤ mainBeta * mainT0 xi := by
    refine hCb.2.trans ?_
    unfold mainT0
    calc Real.sqrt (∫ ω, Bs ω ∂μ) * Real.sqrt (∫ ω, Bs ω * V2 ω ∂μ) ≤
        Real.sqrt mainBeta * Real.sqrt (mainBeta * xi) :=
          mul_le_mul (Real.sqrt_le_sqrt hEB) (Real.sqrt_le_sqrt hBVle) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = mainBeta * Real.sqrt xi := by
          rw [← Real.sqrt_mul hβ, ← mul_assoc, Real.sqrt_mul (mul_nonneg hβ hβ),
            Real.sqrt_mul_self hβ]
  have hBDmInt : Integrable (fun ω => Bs ω * Dm ω) μ := by
    have : (fun ω => Bs ω * Dm ω) = fun ω => ka * (Bs ω * Real.sqrt (Bs ω * Dr ω)) +
        kd * (Bs ω * Real.sqrt (V2 ω)) := by
      funext ω; simp only [Dm]; ring
    rw [this]
    exact (hCa.1.const_mul ka).add (hCb.1.const_mul kd)
  have hBd : (∫ ω, Bs ω * Dm ω ∂μ) ≤ mainBeta * mainLoadD (b ^ 2) a f H xi (mainKd (b ^ 2)) := by
    have : (∫ ω, Bs ω * Dm ω ∂μ) = ka * (∫ ω, Bs ω * Real.sqrt (Bs ω * Dr ω) ∂μ) +
        kd * (∫ ω, Bs ω * Real.sqrt (V2 ω) ∂μ) := by
      have e : (fun ω => Bs ω * Dm ω) = fun ω => ka * (Bs ω * Real.sqrt (Bs ω * Dr ω)) +
          kd * (Bs ω * Real.sqrt (V2 ω)) := by
        funext ω; simp only [Dm]; ring
      rw [e, integral_add (hCa.1.const_mul ka) (hCb.1.const_mul kd), integral_const_mul,
        integral_const_mul]
    rw [this]
    unfold mainLoadD
    calc ka * (∫ ω, Bs ω * Real.sqrt (Bs ω * Dr ω) ∂μ) +
          kd * (∫ ω, Bs ω * Real.sqrt (V2 ω) ∂μ) ≤
        ka * (mainBeta * mainR1 a f H) + kd * (mainBeta * mainT0 xi) :=
          add_le_add (mul_le_mul_of_nonneg_left hAle hka) (mul_le_mul_of_nonneg_left hBle hkd)
      _ = _ := by ring
  -- (2) E[B Dm²] ≤ z²
  have hGlobal := hot_memLp_const_mul_sqrt μ (fun ω => Bs ω ^ 2 * Dr ω)
    (fun ω => mul_nonneg (sq_nonneg _) (hDr0 ω)) hsplit.2.2.1
    (mainBeta ^ 2 * (a - f) + (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
      (H / (1 - mainAlpha))) ka hsplit.2.2.2 hka
  have h0 : 0 ≤ mainEpsNew * mainD * mainBeta * H := by
    have hH : 0 ≤ H := (le_trans lpNorm_nonneg (hHist t ht).2.2)
    have hAlpha : 0 ≤ mainAlpha := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    have hD : 0 ≤ mainD := by dsimp [mainD]; exact add_nonneg (by norm_num) hAlpha
    have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
    positivity
  have hMixed := hot_memLp_const_mul_sqrt μ (fun ω => Bs ω * V2 ω)
    (fun ω => mul_nonneg (hBs0 ω) (hV20 ω)) hBVint
    (mainBeta * xi + mainEpsNew * mainD * mainBeta * H) kd (by linarith) hkd
  let X : Cutoff.CutoffSample 2 → ℝ := fun ω => Real.sqrt (Bs ω ^ 2 * Dr ω)
  let Y : Cutoff.CutoffSample 2 → ℝ := fun ω => Real.sqrt (Bs ω * V2 ω)
  have hZ := main_e_source_square_actual_law M (b ^ 2) a f H xi X Y
    (by simpa only [mainR2, mainHd] using hGlobal) hMixed
  have hBDm2 : (fun ω => Bs ω * Dm ω ^ 2) = fun ω => (ka * X ω + kd * Y ω) ^ 2 := by
    funext ω
    have hB := hBs0 ω
    have e1 : X ω = Real.sqrt (Bs ω) * Real.sqrt (Bs ω * Dr ω) := by
      simp only [X]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB, Real.sqrt_mul hB, ← mul_assoc,
        Real.mul_self_sqrt hB]
    have e2 : Y ω = Real.sqrt (Bs ω) * Real.sqrt (V2 ω) := Real.sqrt_mul hB _
    have e3 : ka * X ω + kd * Y ω = Real.sqrt (Bs ω) * Dm ω := by
      rw [e1, e2]; simp only [Dm]; ring
    rw [e3, mul_pow, Real.sq_sqrt hB]
  have hBDm2int : Integrable (fun ω => Bs ω * Dm ω ^ 2) μ := by
    rw [hBDm2]; exact hZ.2.1.integrable_sq
  have hBDm2le : (∫ ω, Bs ω * Dm ω ^ 2 ∂μ) ≤ mainLoadZ (b ^ 2) a f H xi (mainKd (b ^ 2)) ^ 2 := by
    rw [hBDm2]; exact hZ.2.2
  -- (3) E[B Gt Dm] ≤ z r_ec
  have hXg : Integrable (fun ω => Bs ω * (2 * Th ω)) μ := by
    have := hBTint.const_mul 2
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hXgle : (∫ ω, Bs ω * (2 * Th ω) ∂μ) ≤ 2 * mainBeta * xi := by
    have e : (fun ω => Bs ω * (2 * Th ω)) = fun ω => 2 * (Bs ω * Th ω) := by
      funext ω; ring
    rw [e, integral_const_mul]
    have : (∫ ω, Bs ω * Th ω ∂μ) ≤ mainBeta * xi := hBTle
    linarith
  have hCg := main_cauchy_sqrt_expectation μ (fun ω => Bs ω * (2 * Th ω))
    (fun ω => Bs ω * Dm ω ^ 2) hXg hBDm2int
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hBs0 ω) (mul_nonneg (by norm_num) (hTh0 ω)))
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hBs0 ω) (sq_nonneg _))
  have eG : (fun ω => Real.sqrt (Bs ω * (2 * Th ω)) * Real.sqrt (Bs ω * Dm ω ^ 2)) =
      fun ω => Bs ω * Gt ω * Dm ω := by
    funext ω
    have hB := hBs0 ω
    rw [Real.sqrt_mul hB, Real.sqrt_mul hB, Real.sqrt_sq (hDm0 ω)]
    show _ = Bs ω * Real.sqrt (2 * Th ω) * Dm ω
    have := Real.mul_self_sqrt hB
    calc Real.sqrt (Bs ω) * Real.sqrt (2 * Th ω) * (Real.sqrt (Bs ω) * Dm ω)
        = (Real.sqrt (Bs ω) * Real.sqrt (Bs ω)) * Real.sqrt (2 * Th ω) * Dm ω := by ring
      _ = _ := by rw [this]
  rw [eG] at hCg
  have hz0 := hZ.1
  have hBGd : (∫ ω, Bs ω * Gt ω * Dm ω ∂μ) ≤
      mainLoadZ (b ^ 2) a f H xi (mainKd (b ^ 2)) * mainRec xi := by
    refine hCg.2.trans ?_
    rw [mul_comm]
    unfold mainRec
    exact mul_le_mul (by
      calc Real.sqrt (∫ ω, Bs ω * Dm ω ^ 2 ∂μ) ≤ Real.sqrt (mainLoadZ (b ^ 2) a f H xi
            (mainKd (b ^ 2)) ^ 2) := Real.sqrt_le_sqrt hBDm2le
        _ = _ := Real.sqrt_sq hz0)
      (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) hz0
  -- pathwise domination
  have hpt : ∀ ω, mainHotFeedbackRow M m hobs t b ω ≤
      2 * kd * (63 / 50) * (Real.sqrt 2 * (Bs ω * Dm ω) + Bs ω * Gt ω * Dm ω) := by
    intro ω
    have hrow := main_hot_feedback_row_le M m hobs h40 t ht b ω
    have hd : mainHotSourceRms M m hobs t b ω ≤ Dm ω := by
      have hdom := main_hot_source_size_sq_le_dom M m hobs h40 t ht b ω
      unfold mainHotSourceRms
      calc Real.sqrt _ ≤ Real.sqrt (Dm ω ^ 2) := Real.sqrt_le_sqrt hdom
        _ = Dm ω := Real.sqrt_sq (hDm0 ω)
    have hg : mainHotReciprocalRms M m hobs t ω ≤ Gt ω :=
      hot_reciprocal_rms_le_theta M hγ m hobs h40 t ht ω
    have hd0 := mainHotSourceRms_nonneg M m hobs t b ω
    have hc : 0 ≤ 2 * kd * (63 / 50) := by positivity
    refine hrow.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (hBs0 ω)) (Real.sqrt_nonneg _))
      (mul_le_mul (mul_le_mul_of_nonneg_left hg (hBs0 ω)) hd hd0
        (mul_nonneg (hBs0 ω) (hGt0 ω)))) hc)
  have hWint : Integrable (fun ω => 2 * kd * (63 / 50) *
      (Real.sqrt 2 * (Bs ω * Dm ω) + Bs ω * Gt ω * Dm ω)) μ :=
    ((hBDmInt.const_mul (Real.sqrt 2)).add hCg.1).const_mul _
  have hW0 : ∀ ω, 0 ≤ 2 * kd * (63 / 50) *
      (Real.sqrt 2 * (Bs ω * Dm ω) + Bs ω * Gt ω * Dm ω) := fun ω => by
    have := hBs0 ω; have := hGt0 ω; have := hDm0 ω
    positivity
  have hmono : (∫ ω, mainHotFeedbackRow M m hobs t b ω ∂μ) ≤
      ∫ ω, 2 * kd * (63 / 50) * (Real.sqrt 2 * (Bs ω * Dm ω) + Bs ω * Gt ω * Dm ω) ∂μ := by
    by_cases hI : Integrable (mainHotFeedbackRow M m hobs t b) μ
    · exact integral_mono_ae hI hWint (Filter.Eventually.of_forall hpt)
    · rw [integral_undef hI]
      exact integral_nonneg hW0
  refine hmono.trans ?_
  have hlin : (∫ ω, 2 * kd * (63 / 50) *
      (Real.sqrt 2 * (Bs ω * Dm ω) + Bs ω * Gt ω * Dm ω) ∂μ) =
      2 * kd * (63 / 50) * (Real.sqrt 2 * (∫ ω, Bs ω * Dm ω ∂μ) +
        (∫ ω, Bs ω * Gt ω * Dm ω ∂μ)) := by
    rw [integral_const_mul, integral_add (hBDmInt.const_mul _) hCg.1, integral_const_mul]
  rw [hlin]
  exact main_e_remainder_feedback_actual_law M Bs Dm Gt (b ^ 2) a f H xi hBd hBGd

end
end ASDExplicitGamma.Main
end
