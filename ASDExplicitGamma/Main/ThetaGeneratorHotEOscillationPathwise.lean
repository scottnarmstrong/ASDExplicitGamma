module

public import ASDExplicitGamma.Main.HotETermOscCarrier
public import ASDExplicitGamma.Main.HotPatchSourcePositive
public import ASDExplicitGamma.Main.HotPatchSourceBoundCells
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsDrop

/-! Pathwise bound of the oscillatory C-group of the hot-patched trial by
`2 (k_a (B* Δ)^{1/2} + k_d K^{1/2}) · (descendant average of the joint profile squares)^{1/2}`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

/-- Cauchy-Schwarz for descendant averages. -/
theorem hot_desc_average_mul_le_Th (Q : TriadicCube 2) (depth : ℕ) (f g : TriadicCube 2 → ℝ) :
    descendantsAverage Q depth (fun U => f U * g U) ≤
      Real.sqrt (descendantsAverage Q depth (fun U => f U ^ 2)) *
        Real.sqrt (descendantsAverage Q depth (fun U => g U ^ 2)) := by
  show ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q depth, f U * g U ≤
    Real.sqrt (((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q depth, f U ^ 2) *
      Real.sqrt (((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q depth, g U ^ 2)
  set s := descendantsAtDepth Q depth
  set c : ℝ := ((s.card : ℝ))⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.2 (Nat.cast_nonneg _)
  have hcs : c = Real.sqrt c * Real.sqrt c := (Real.mul_self_sqrt hc0).symm
  have hcs' := Real.sum_mul_le_sqrt_mul_sqrt s f g
  calc c * ∑ U ∈ s, f U * g U ≤ c * (Real.sqrt (∑ U ∈ s, f U ^ 2) * Real.sqrt (∑ U ∈ s, g U ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs' hc0
    _ = Real.sqrt (c * ∑ U ∈ s, f U ^ 2) * Real.sqrt (c * ∑ U ∈ s, g U ^ 2) := by
        rw [Real.sqrt_mul hc0, Real.sqrt_mul hc0]
        nth_rewrite 1 [hcs]
        ring

theorem hot_desc_average_const_mul_Th (Q : TriadicCube 2) (depth : ℕ) (c : ℝ)
    (f : TriadicCube 2 → ℝ) :
    descendantsAverage Q depth (fun U => c * f U) = c * descendantsAverage Q depth f := by
  show ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q depth, c * f U =
    c * (((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q depth, f U)
  rw [← Finset.mul_sum]
  ring

theorem hot_source_size_sq_average_Th (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hsrc : ∀ (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q depth),
      Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
        vectorPositiveHaarNorm U (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L
          n (blockBasis c) x).2) ^ 2)) :
    descendantsAverage Q depth (fun U => hotSourceSize (fun n P x =>
        hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U ^ 2) =
      ∑' n, ∑ c : BlockCoord 2, descendantsAverage Q depth (fun U => vectorPositiveHaarEnergy U
        (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2)) := by
  classical
  have e1 : ∀ U ∈ descendantsAtDepth Q depth, hotSourceSize (fun n P x =>
        hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U ^ 2 =
      ∑' n, ∑ c : BlockCoord 2, vectorPositiveHaarEnergy U
        (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2) := by
    intro U hU
    simp only [hotSourceSize]
    rw [Real.sq_sqrt (tsum_nonneg fun n => Finset.sum_nonneg fun c _ => sq_nonneg _)]
    refine tsum_congr fun n => Finset.sum_congr rfl fun c _ => ?_
    simp only [vectorPositiveHaarNorm]
    rw [Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
  rw [main_hot_descendants_average_congr_Th Q depth _ _ e1]
  have hsum : ∀ U ∈ descendantsAtDepth Q depth, Summable (fun n : whiteBasisIndex =>
      ∑ c : BlockCoord 2, vectorPositiveHaarEnergy U
        (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2)) := by
    intro U hU
    refine (hsrc U hU).congr fun n => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [vectorPositiveHaarNorm]
    rw [Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
  show ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q depth, ∑' n,
    ∑ c : BlockCoord 2, vectorPositiveHaarEnergy U
      (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2) = _
  rw [← Summable.tsum_finsetSum hsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [main_descendantsAverage_finset_sum_univ]
  rfl


/-- The cell average of the absolute values of the hot oscillatory carrier sums. -/
def hotOscRow_Th (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu)
    (hsigma : 0 < sigma) (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) : ℝ :=
  descendantsAverage Q depth (fun U =>
    if hU : U ∈ descendantsAtDepth Q depth then
      |∑' n : whiteBasisIndex, mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma
        hnu hsigma k b L (fun n P x => hotPatchSource Q depth depth nu sigma hnu hsigma k b L
          n P x) n ⟨U, hU⟩|
    else 0)

theorem hot_osc_row_le_size_Th (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hsrc : ∀ (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q depth),
      Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
        vectorPositiveHaarNorm U (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L
          n (blockBasis c) x).2) ^ 2)) :
    hotOscRow_Th Q depth nu sigma hnu hsigma k b L ≤
      2 * (Real.sqrt (descendantsAverage Q depth (fun U => hotSourceSize (fun n P x =>
        hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U ^ 2)) *
        Real.sqrt (descendantsAverage Q depth (fun U =>
          mainOldJointOscillationProfile Q U nu sigma k b L ^ 2))) := by
  classical
  have hH : ∀ n P, MemBlockL2 (openCubeSet Q)
      (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P) :=
    fun n P => hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n P
  have hpos := fun n P U hU j => hot_source_positive_series Q depth nu sigma hnu hsigma k b L n
    P U hU j
  have hcell : ∀ U ∈ descendantsAtDepth Q depth, (if hU : U ∈ descendantsAtDepth Q depth then
      |∑' n : whiteBasisIndex, mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma
        hnu hsigma k b L (fun n P x => hotPatchSource Q depth depth nu sigma hnu hsigma k b L
          n P x) n ⟨U, hU⟩| else 0) ≤
      2 * (hotSourceSize (fun n P x =>
        hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U *
        mainOldJointOscillationProfile Q U nu sigma k b L) := by
    intro U hU
    rw [dif_pos hU]
    have := (main_e_actual_oscillatory_cross_2dq_hot Q depth nu sigma hnu hsigma k b L
      (fun n P x => hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) hH
      hpos hsrc ⟨U, hU⟩).2
    rw [mul_assoc] at this
    exact this
  have hrow := descendantsAverage_le hcell
  rw [hot_desc_average_const_mul_Th] at hrow
  exact hrow.trans (mul_le_mul_of_nonneg_left (hot_desc_average_mul_le_Th Q depth _ _)
    (by norm_num))

theorem hot_osc_row_pathwise_Th (mm : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 mm) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (Bmax : ℝ)
    (hB : ∀ (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 mm) depth),
      oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma
        (oldSignedCellCoefficient (originCube 2 mm) U
          (openCubeSet_subset_of_mem_descendantsAtDepth hU) k)) ≤ Bmax) :
    hotOscRow_Th (originCube 2 mm) depth nu sigma hnu hsigma k b L ≤
      2 * ((oldSignedSourceMultiplier (originCube 2 mm) depth b L *
          Real.sqrt (Bmax * (descendantsAverage (originCube 2 mm) depth (fun U =>
              traceDefect (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k) 1) -
            traceDefect (openCubeSet (originCube 2 mm))
              (responseFramePlanarCoefficientField nu sigma k) 1)) +
        mainKd (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy (originCube 2 mm) depth
          (hotGluedCorrector (originCube 2 mm) depth nu sigma hnu hsigma k
            (blockBasis c)).toH1Function.grad)) *
        Real.sqrt (descendantsAverage (originCube 2 mm) depth (fun U =>
          mainOldJointOscillationProfile (originCube 2 mm) U nu sigma k b L ^ 2))) := by
  classical
  have hsrc := fun U hU => hot_source_cell_summable mm depth nu sigma hnu hsigma k b L hL U hU
  obtain ⟨hs, hbound⟩ := hot_source_size_bound_of_cells mm depth nu sigma hnu hsigma k b L hL Bmax hB
  have hs2 := hot_source_size_sq_average_Th (originCube 2 mm) depth nu sigma hnu hsigma k b L hsrc
  have hrow := hot_osc_row_le_size_Th (originCube 2 mm) depth nu sigma hnu hsigma k b L hsrc
  rw [hs2] at hrow
  exact hrow.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg _)) (by norm_num))

end

end ASDExplicitGamma.Main
