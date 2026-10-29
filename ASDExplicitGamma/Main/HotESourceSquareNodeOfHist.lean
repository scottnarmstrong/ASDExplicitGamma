module

public import ASDExplicitGamma.Main.HotESourceSquareNode
public import ASDExplicitGamma.Main.HotObsSplitOfHist

/-! Successors of `HotESourceSquareNode` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- Successor of `main_hot_e_source_square` with the history envelope `Hfun`. -/
theorem main_hot_e_source_square_ofHist
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
    (∫ ω, mainHotSourceSquareRow M m hobs t b ω ∂μ) ≤
      mainLoadZ (b ^ 2) a f H xi (mainKd (b ^ 2)) ^ 2 := by
  classical
  intro μ v xi a f H
  let Q := originCube 2 (m + hobs)
  let D := descendantsAtDepth Q (hobs + 5)
  let Bs : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let Dr : Cutoff.CutoffSample 2 → ℝ := mainHotDropObs M m hobs t
  let V2 : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    descendantsAverage Q (hobs + 5) (fun U => mixedBridgeVLocal M m U t ω ^ 2)
  let X : Cutoff.CutoffSample 2 → ℝ := fun ω => Real.sqrt (Bs ω ^ 2 * Dr ω)
  let Y : Cutoff.CutoffSample 2 → ℝ := fun ω => Real.sqrt (Bs ω * V2 ω)
  have hsplit := main_hot_obs_positive_split_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs t ht
  have hbs : mixedGlobalHistoryMax M m t = Bs :=
    funext fun ω => main_hot_bstar_eq M m t ht ω
  rw [hbs] at hsplit
  have hBs : ∀ ω, 0 ≤ Bs ω := fun ω => mixed_bridge_bstar_nonneg M m t ω
  have hDr : ∀ ω, 0 ≤ Dr ω := fun ω => (main_hot_drop_obs_pathwise M m hobs t ω).2
  have hka : 0 ≤ mainKa (b ^ 2) := by unfold mainKa mainA2; positivity
  have hkd : 0 ≤ mainKd (b ^ 2) := mainKd_nonneg _
  -- global side
  have hGlobal := hot_memLp_const_mul_sqrt μ (fun ω => Bs ω ^ 2 * Dr ω)
    (fun ω => mul_nonneg (sq_nonneg _) (hDr ω)) hsplit.2.2.1
    (mainBeta ^ 2 * (a - f) + (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) *
      (H / (1 - mainAlpha))) (mainKa (b ^ 2)) hsplit.2.2.2 hka
  -- mixed side
  have hcell : ∀ U ∈ D, Integrable (fun ω => Bs ω * mixedBridgeVLocal M m U t ω ^ 2) μ ∧
      (∫ ω, Bs ω * mixedBridgeVLocal M m U t ω ^ 2 ∂μ) ≤ mainBeta * xi :=
    fun U hU => hot_obs_cell_weighted_moment M h hM hγ N hpast m hm hobs h40 t ht U hU
  have hu2eq : (fun ω => Bs ω * V2 ω) = fun ω => ((D.card : ℝ)⁻¹) *
      ∑ U ∈ D, Bs ω * mixedBridgeVLocal M m U t ω ^ 2 := by
    funext ω
    show Bs ω * (((D.card : ℝ)⁻¹) * ∑ U ∈ D, mixedBridgeVLocal M m U t ω ^ 2) = _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    ring
  have hsumInt : Integrable (fun ω => ∑ U ∈ D, Bs ω * mixedBridgeVLocal M m U t ω ^ 2) μ :=
    integrable_finset_sum D fun U hU => (hcell U hU).1
  have hu2Int : Integrable (fun ω => Bs ω * V2 ω) μ := by
    rw [hu2eq]
    exact hsumInt.const_mul _
  have hu2Cap : (∫ ω, Bs ω * V2 ω ∂μ) ≤ mainBeta * xi + mainEpsNew * mainD * mainBeta * H := by
    rw [hu2eq, integral_const_mul, integral_finset_sum D fun U hU => (hcell U hU).1]
    have hcard : ((D.card : ℝ)⁻¹) * ∑ U ∈ D, (∫ ω, Bs ω * mixedBridgeVLocal M m U t ω ^ 2 ∂μ) ≤
        mainBeta * xi := by
      have hle := Finset.sum_le_card_nsmul D _ (mainBeta * xi) fun U hU => (hcell U hU).2
      have hpos : (0 : ℝ) < D.card :=
        by exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty Q (hobs + 5))
      rw [nsmul_eq_mul] at hle
      calc ((D.card : ℝ)⁻¹) * _ ≤ ((D.card : ℝ)⁻¹) * (D.card * (mainBeta * xi)) :=
            mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hpos.le)
        _ = mainBeta * xi := by field_simp
    refine hcard.trans ?_
    have h0 : 0 ≤ mainEpsNew * mainD * mainBeta * H := by
      have hH : 0 ≤ H := (le_trans lpNorm_nonneg (hHist t ht).2.2)
      have hAlpha : 0 ≤ mainAlpha := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      have hD : 0 ≤ mainD := by dsimp [mainD]; exact add_nonneg (by norm_num) hAlpha
      have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
      have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
      positivity
    linarith
  have hMixed := hot_memLp_const_mul_sqrt μ (fun ω => Bs ω * V2 ω)
    (fun ω => mul_nonneg (hBs ω) (by
      show 0 ≤ ((D.card : ℝ)⁻¹) * ∑ U ∈ D, mixedBridgeVLocal M m U t ω ^ 2
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun U _ => sq_nonneg _))) hu2Int _ (mainKd (b ^ 2)) hu2Cap hkd
  have hZ := main_e_source_square_actual_law M (b ^ 2) a f H xi X Y
    (by simpa only [mainR2, mainHd] using hGlobal) hMixed
  have hInt : Integrable (fun ω => (mainKa (b ^ 2) * X ω + mainKd (b ^ 2) * Y ω) ^ 2) μ :=
    hZ.2.1.integrable_sq
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ω => mainHotSourceSquareRow_nonneg M m hobs t b ω))
    hInt (Filter.Eventually.of_forall (fun ω =>
      main_hot_source_square_row_le M m hobs h40 t ht b ω))
  exact hmono.trans hZ.2.2

end
end ASDExplicitGamma.Main
end
