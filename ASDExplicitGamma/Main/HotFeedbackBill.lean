module

public import ASDExplicitGamma.Main.HotSourceEnergy
public import ASDExplicitGamma.Native.OldSignedGlobalOldSourceFeedback
public import ASDExplicitGamma.Native.OldSignedHalfGain
public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback
public import ASDExplicitGamma.Native.OldSignedSeriesLinearBudget
public import ASDExplicitGamma.Native.OldSignedReciprocalLoadBudget

/-! The derivative feedback of the hot source `f'` (the remainder `R'` feedback group of the
hot trial) is summable and bounded by the cell average of
`kappa_U (sqrt 2 + G_U) (1/2 + alpha) B_U d'_U`.  Generic-source, half-gain copy of
`old_signed_global_old_source_feedback_bill`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

/-- Cellwise feedback bill of the hot source with the half-gain constant. -/
theorem hot_source_cell_feedback_bill (mm : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 mm) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 mm) depth) :
    let Q := originCube 2 mm
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := fun n c => hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c)
    let R := fun n c => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k (F n c)
      (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))
    let f := fun n => ∑ c : BlockCoord 2, oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (R n c))
    Summable f ∧ |∑' n, f n| ≤
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
        (Real.sqrt 2 + oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k) *
        ((1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a *
          hotSourceSize (fun n P x =>
            hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U) := by
  intro Q hsub a kU F R f
  classical
  have hFm : ∀ n c, MemBlockL2 (openCubeSet Q) (F n c) := fun n c =>
    hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis c)
  have hF1 : ∀ n c x, (F n c x).1 = 0 := fun n c x =>
    congrArg Prod.fst (congrFun
      (hot_source_eq_zero_second Q depth nu sigma hnu hsigma k b L n (blockBasis c)) x)
  let u := fun n c => oldSignedCellFirstCorrector Q U hsub nu sigma hnu hsigma k (F n c) (hFm n c)
  let p := fun (n : whiteBasisIndex) (c : BlockCoord 2) =>
    vectorPositiveHaarNorm U (fun x => (F n c x).2)
  let g := fun (n : whiteBasisIndex) (c : BlockCoord 2) =>
    vectorWeakHaarNorm U (u n c).toH1Function.grad
  have hps : Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2, p n c ^ 2) :=
    hot_source_cell_summable mm depth nu sigma hnu hsigma k b L hL U hU
  have hB : 0 ≤ oldSignedInverseHistory U a :=
    lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hα := inverse_history_discount_range
  have hD : 0 ≤ 1 / 2 + inverseHistoryDiscount := by linarith [hα.1]
  have hgc : ∀ n c, g n c ≤ ((1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a) *
      p n c + 0 * p n c := by
    intro n c
    let gg := fun x => (F n c x).2
    have hFeq := hot_source_eq_zero_second Q depth nu sigma hnu hsigma k b L n (blockBasis c)
    have hFparent := hFm n c
    have hF0 : MemBlockL2 (openCubeSet Q) (fun x => (0, gg x)) := by
      rw [← hFeq]
      exact hFparent
    have hFU : MemBlockL2 (openCubeSet U) (fun x => (0, gg x)) :=
      hF0.mono_measure (Measure.restrict_mono_set volume hsub)
    have hp : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) * energy U
        (cubeIncrement U (j + 1) (fun x => gg x i))) := by
      intro i
      refine (hot_source_positive_series Q depth nu sigma hnu hsigma k b L n (blockBasis c)
        U hU i).congr fun d => ?_
      simp only [Triadic.cubeIncrement_neg, Triadic.energy_neg]
      rfl
    have hres : oldSignedCellResidual Q U hsub nu sigma hnu hsigma k (F n c) (hFm n c) =
        scalarResidualField U nu sigma hnu hsigma kU (toHilbertBlockL2OfBlockField hFU) := by
      have := hot_cell_residual_congr Q U hsub nu sigma hnu hsigma k (F n c)
        (fun x => (0, gg x)) hFeq hFparent hF0
      rw [this]
      rfl
    have hgrad := old_signed_cell_first_corrector_grad Q U hsub nu sigma hnu hsigma k (F n c)
      (hFm n c)
    have hv : (fun x => (scalarResidualField U nu sigma hnu hsigma kU
        (toHilbertBlockL2OfBlockField hFU) x).1) =ᵐ[volumeMeasureOn (openCubeSet U)]
        (u n c).toH1Function.grad := by
      refine Filter.Eventually.of_forall fun x => ?_
      change _ = (oldSignedCellFirstCorrector Q U hsub nu sigma hnu hsigma k (F n c)
        (hFm n c)).toH1Function.grad x
      rw [hgrad]
      change _ = _ - (F n c x).1
      rw [hF1 n c x, sub_zero, hres]
    have h1 := old_signed_pure_second_sharp_first_halfgain U nu sigma hnu hsigma kU gg hFU hp
      (u n c) hv
    have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
    rw [hs.1] at h1
    simpa only [zero_mul, add_zero, g, p, mul_assoc] using h1
  have hfirst := old_signed_load_series_linear_budget p p g
    ((1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a) 0
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (mul_nonneg hD hB) le_rfl hps hps hgc
  have hu : ∀ c, Summable (fun n => vectorWeakHaarNorm U (u n c).toH1Function.grad ^ 2) := by
    intro c
    refine hfirst.1.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    exact Finset.single_le_sum (f := fun c' => g n c' ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ c)
  have hh := old_signed_complete_cell_correction_feedback Q U hsub nu sigma hnu hsigma k
    blockBasis b L F hFm hu
  have hz (n : whiteBasisIndex) (c : BlockCoord 2) :
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (F n c) = 0 := by
    funext x
    change (0, -(_ • matVecMul responsePlanarJ (F n c x).1)) = (0, 0)
    rw [hF1 n c x, matVecMul_zero, smul_zero, neg_zero]
  have hfc : (fun n => ∑ c : BlockCoord 2, oldSignedEnergyPairing U nu sigma
      (oldSignedCellCoefficient Q U hsub k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((R n c : Vec 2 → BlockVec 2) - F n c))) = f := by
    funext n
    apply Finset.sum_congr rfl
    intro c _
    rw [map_sub, hz, sub_zero]
  have hresult : Summable f ∧ |∑' n, f n| ≤
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
        Real.sqrt (∑ c : BlockCoord 2, vectorWeakHaarNorm U
          (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k
            (blockBasis c)).grad ^ 2) *
        Real.sqrt (∑ c : BlockCoord 2, ∑' n : whiteBasisIndex,
          vectorWeakHaarNorm U (u n c).toH1Function.grad ^ 2) := by
    have := hh
    rw [hfc] at this
    exact this
  have heq : (∑ c : BlockCoord 2, ∑' n : whiteBasisIndex,
      vectorWeakHaarNorm U (u n c).toH1Function.grad ^ 2) =
      ∑' n : whiteBasisIndex, ∑ c : BlockCoord 2,
        vectorWeakHaarNorm U (u n c).toH1Function.grad ^ 2 :=
    (Summable.tsum_finsetSum (fun c _ => hu c)).symm
  rw [heq] at hresult
  have hg := old_signed_actual_reciprocal_load_budget Q U hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  have hgnonneg : 0 ≤ Real.sqrt 2 + oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb : Real.sqrt (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2,
      vectorWeakHaarNorm U (u n c).toH1Function.grad ^ 2) ≤
      (1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a *
        hotSourceSize (fun n P x =>
          hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U := by
    have := hfirst.2
    simpa only [zero_mul, add_zero, mul_zero, hotSourceSize, p, F, g] using this
  exact ⟨hresult.1, hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hb
    (Real.sqrt_nonneg _) (mul_nonneg hκ hgnonneg))⟩

/-- The feedback group of the hot source is summable and bounded by the cell average of the
cell bills. -/
theorem hot_source_feedback_bill (mm : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 mm) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1) :
    let Q := originCube 2 mm
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n => (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).feedbackSource n
    Summable f ∧ |∑' n, f n| ≤ descendantsAverage Q depth (fun U =>
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
        (Real.sqrt 2 + oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k) *
        ((1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a *
          hotSourceSize (fun n P x =>
            hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U)) := by
  classical
  intro Q a f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : BlockCoord 2, oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
          (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis i))
          (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis i))))
  have he : f = (fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    exact old_signed_patched_feedback_load_partition Q depth nu sigma hnu hsigma k b L n
      (fun i : BlockCoord 2 => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis i))
      (fun i => hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis i))
      (fun _ => Lp.memLp _)
      (fun i => hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis i))
  rw [he, ← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_bound Q depth fc _
    (fun U => (hot_source_cell_feedback_bill mm depth nu sigma hnu hsigma k b L hL U.val
      U.property).1)
    (fun U => (hot_source_cell_feedback_bill mm depth nu sigma hnu hsigma k b L hL U.val
      U.property).2)

end

end ASDExplicitGamma.Main
