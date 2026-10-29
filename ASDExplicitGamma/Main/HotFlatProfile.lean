module

public import ASDExplicitGamma.Main.EOscillationFlatOscillationCaps
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import ASDExplicitGamma.Main.FlatFieldSourceCaps

/-! Hot trial: oscillation caps of the actual centered flat rows at the actual shell
length (`L` with `3^6 r ≤ L` for the depth cells). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

theorem main_hilbert_flat_row_q3_eq_sqrt3_hotcopy :
    (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 := by
  rw [show 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow]

theorem main_cubeAverage_neg_sourceFlat_hotcopy
    (U : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage U (fun x => -f x) = -cubeAverage U f := by
  unfold cubeAverage
  rw [integral_neg]
  ring

theorem main_oldSignedFlatPlus_mode_energy_eq_hilbertCirc_hotcopy
    (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : Gaussian.whiteBasisIndex) :
    (∑ i : Fin 2, oldSignedBlockPositiveNorm U
      (oldSignedFlatPlusBlock Q b L n i - fun _ =>
        oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)) ^ 2) =
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatPlusH1 Q b L n).toFun ^ 2 := by
  let uQ := mainFlatPlusH1 Q b L n
  let hsub : openCubeSet U ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hU
  let uU := uQ.restrict hsub (measurableSet_openCubeSet Q)
  have hu : MemLp uU.toFun 2 (normalizedCubeMeasure U) := by
    apply (memLp_piLp_iff).2
    intro a
    change MemLp (fun x => (uU.toFun x).ofLp a) 2 (normalizedCubeMeasure U)
    let P : EuclideanSpace ℝ (Fin 2 × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin 2 × Fin 2 => ℝ) a
    have hp := P.comp_memLp' uU.memL2
    have hpn := memLp_normalized_of_memL2On hp
    convert hpn using 1
    funext x
    simp [P]
  have hq : 1 < (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) := by
    calc
      1 < Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
      _ = (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) :=
        main_hilbert_flat_row_q3_eq_sqrt3_hotcopy.symm
  have hq9 : (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) < 9 := by
    calc
      (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 :=
        main_hilbert_flat_row_q3_eq_sqrt3_hotcopy
      _ < 9 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
  have hseriesQ := (hilbert_positive_poincare_of_weight U hq hq9 uU).1
  have hseries : Summable (fun k => (Real.sqrt 3)^(k+1) *
      hilbertEnergy U (hilbertCubeIncrement U (k+1) uU.toFun)) := by
    simpa only [main_hilbert_flat_row_q3_eq_sqrt3_hotcopy] using hseriesQ
  have hraw := main_hilbertPrimalEnergy_euclidean U hu hseries
  have hroot0 : hilbertEnergy U (hilbertCubeIncrement U 0 uU.toFun) =
      ∑ a : Fin 2 × Fin 2,
        (cubeAverage U (fun x => (uU.toFun x).ofLp a)) ^ 2 := by
    have h := main_hilbertEnergy_euclidean U
      (hilbertCubeIncrement_memLp U 0 uU.toFun)
    simp_rw [← main_hilbertIncrement_coordinate U hu 0] at h
    simpa only [cubeIncrement_zero, energy_projection_zero] using h
  have hblock (i : Fin 2) :
      MemBlockL2 (openCubeSet U) (oldSignedFlatPlusBlock Q b L n i) :=
    (old_signed_flat_plus_block_memL2 Q b L n i).mono_measure
      (Measure.restrict_mono_set volume hsub)
  have hcentered :
      (∑ i : Fin 2, oldSignedBlockPositiveNorm U
        (oldSignedFlatPlusBlock Q b L n i - fun _ =>
          oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)) ^ 2) =
      (∑ i : Fin 2, oldSignedBlockPositiveNorm U
        (oldSignedFlatPlusBlock Q b L n i) ^ 2) -
      ∑ i : Fin 2, blockVecDot
        (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))
        (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)) := by
    calc
      _ = ∑ i : Fin 2,
          (oldSignedBlockPositiveNorm U (oldSignedFlatPlusBlock Q b L n i) ^ 2 -
            blockVecDot (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))
              (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact old_signed_block_positive_centering U
          (oldSignedFlatPlusBlock Q b L n i) (hblock i)
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hrawEq :
      (∑ i : Fin 2, oldSignedBlockPositiveNorm U
        (oldSignedFlatPlusBlock Q b L n i) ^ 2) =
        hilbertPrimalEnergy U (Real.sqrt 3) uU.toFun := by
    calc
      _ = ∑ i : Fin 2, ∑ k : Fin 2,
          primalEnergy U (Real.sqrt 3)
            (mainFlatPlusCoordinate Q b L n (i, k)).toFun := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [old_signed_block_positive_norm_sq]
        simp [oldSignedFlatPlusBlock, old_signed_primal_zero, primalEnergy_neg]
      _ = ∑ a : Fin 2 × Fin 2, primalEnergy U (Real.sqrt 3)
          (mainFlatPlusCoordinate Q b L n a).toFun := by
        rw [Fintype.sum_prod_type]
      _ = ∑ a : Fin 2 × Fin 2, primalEnergy U (Real.sqrt 3)
          (fun x => (uU.toFun x).ofLp a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [show (fun x => (uU.toFun x).ofLp a) =
          (mainFlatPlusCoordinate Q b L n a).toFun by rfl]
      _ = _ := hraw.symm
  have hmeanEq :
      (∑ i : Fin 2, blockVecDot
        (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))
        (oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))) =
      hilbertEnergy U (hilbertCubeIncrement U 0 uU.toFun) := by
    calc
      _ = ∑ a : Fin 2 × Fin 2,
          (cubeAverage U (fun x => (uU.toFun x).ofLp a)) ^ 2 := by
        calc
          _ = ∑ i : Fin 2, ∑ k : Fin 2,
                (cubeAverage U (fun x =>
                  (uU.toFun x).ofLp (i, k))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [oldSignedFlatPlusBlock, oldSignedBlockMean,
              blockVecDot, vecDot, Prod.fst, Prod.snd]
            have hcoordsum :
                (∑ k : Fin 2,
                  cubeAverage U (fun x =>
                    -(mainFlatPlusCoordinate Q b L n (i, k)).toFun x) *
                  cubeAverage U (fun x =>
                    -(mainFlatPlusCoordinate Q b L n (i, k)).toFun x)) =
                (∑ k : Fin 2,
                  cubeAverage U (fun x => (uU.toFun x).ofLp (i, k)) *
                  cubeAverage U (fun x => (uU.toFun x).ofLp (i, k))) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [main_cubeAverage_neg_sourceFlat_hotcopy,
                show (fun x => (uU.toFun x).ofLp (i, k)) =
                  (mainFlatPlusCoordinate Q b L n (i, k)).toFun by rfl]
              ring
            rw [hcoordsum]
            simp [cubeAverage_const, pow_two]
          _ = _ := by rw [Fintype.sum_prod_type]
      _ = _ := hroot0.symm
  have hcircNonneg :
      0 ≤ hilbertPrimalCircEnergy U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) uU.toFun := by
    unfold hilbertPrimalCircEnergy
    apply tsum_nonneg
    intro k
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (hilbertEnergy_nonneg U _)
  calc
    _ = hilbertPrimalEnergy U (Real.sqrt 3) uU.toFun -
        hilbertEnergy U (hilbertCubeIncrement U 0 uU.toFun) := by
      rw [hcentered, hrawEq, hmeanEq]
    _ = hilbertPrimalCircEnergy U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) uU.toFun := by
      rw [← main_hilbert_flat_row_q3_eq_sqrt3_hotcopy]
      simp only [hilbertPrimalEnergy, hilbertPrimalCircEnergy]
      ring
    _ = hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        uU.toFun ^ 2 := by
      rw [hilbertPositiveCircHaarNorm, Real.sq_sqrt hcircNonneg]
    _ = _ := rfl

theorem main_oldSignedFlatMinus_mode_energy_eq_hilbertCirc_hotcopy
    (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : Gaussian.whiteBasisIndex) :
    (∑ i : Fin 2, oldSignedBlockPositiveNorm U
      (oldSignedFlatMinusBlock Q b L n i - fun _ =>
        oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)) ^ 2) =
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatMinusH1 Q b L n).toFun ^ 2 := by
  let uQ := mainFlatMinusH1 Q b L n
  let hsub : openCubeSet U ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hU
  let uU := uQ.restrict hsub (measurableSet_openCubeSet Q)
  have hu : MemLp uU.toFun 2 (normalizedCubeMeasure U) := by
    apply (memLp_piLp_iff).2
    intro a
    change MemLp (fun x => (uU.toFun x).ofLp a) 2 (normalizedCubeMeasure U)
    let P : EuclideanSpace ℝ (Fin 2 × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin 2 × Fin 2 => ℝ) a
    have hp := P.comp_memLp' uU.memL2
    have hpn := memLp_normalized_of_memL2On hp
    convert hpn using 1
    funext x
    simp [P]
  have hq : 1 < (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) := by
    calc
      1 < Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
      _ = (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) :=
        main_hilbert_flat_row_q3_eq_sqrt3_hotcopy.symm
  have hq9 : (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) < 9 := by
    calc
      (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 :=
        main_hilbert_flat_row_q3_eq_sqrt3_hotcopy
      _ < 9 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
  have hseriesQ := (hilbert_positive_poincare_of_weight U hq hq9 uU).1
  have hseries : Summable (fun k => (Real.sqrt 3)^(k+1) *
      hilbertEnergy U (hilbertCubeIncrement U (k+1) uU.toFun)) := by
    simpa only [main_hilbert_flat_row_q3_eq_sqrt3_hotcopy] using hseriesQ
  have hraw := main_hilbertPrimalEnergy_euclidean U hu hseries
  have hroot0 : hilbertEnergy U (hilbertCubeIncrement U 0 uU.toFun) =
      ∑ a : Fin 2 × Fin 2,
        (cubeAverage U (fun x => (uU.toFun x).ofLp a)) ^ 2 := by
    have h := main_hilbertEnergy_euclidean U
      (hilbertCubeIncrement_memLp U 0 uU.toFun)
    simp_rw [← main_hilbertIncrement_coordinate U hu 0] at h
    simpa only [cubeIncrement_zero, energy_projection_zero] using h
  have hblock (i : Fin 2) :
      MemBlockL2 (openCubeSet U) (oldSignedFlatMinusBlock Q b L n i) :=
    (old_signed_flat_minus_block_memL2 Q b L n i).mono_measure
      (Measure.restrict_mono_set volume hsub)
  have hcentered :
      (∑ i : Fin 2, oldSignedBlockPositiveNorm U
        (oldSignedFlatMinusBlock Q b L n i - fun _ =>
          oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)) ^ 2) =
      (∑ i : Fin 2, oldSignedBlockPositiveNorm U
        (oldSignedFlatMinusBlock Q b L n i) ^ 2) -
      ∑ i : Fin 2, blockVecDot
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)) := by
    calc
      _ = ∑ i : Fin 2,
          (oldSignedBlockPositiveNorm U (oldSignedFlatMinusBlock Q b L n i) ^ 2 -
            blockVecDot (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))
              (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact old_signed_block_positive_centering U
          (oldSignedFlatMinusBlock Q b L n i) (hblock i)
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hrawEq :
      (∑ i : Fin 2, oldSignedBlockPositiveNorm U
        (oldSignedFlatMinusBlock Q b L n i) ^ 2) =
        hilbertPrimalEnergy U (Real.sqrt 3) uU.toFun := by
    calc
      _ = ∑ i : Fin 2, ∑ k : Fin 2,
          primalEnergy U (Real.sqrt 3)
            (mainFlatMinusCoordinate Q b L n (i, k)).toFun := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [old_signed_block_positive_norm_sq]
        simp [oldSignedFlatMinusBlock, old_signed_primal_zero, primalEnergy_neg]
      _ = ∑ a : Fin 2 × Fin 2, primalEnergy U (Real.sqrt 3)
          (mainFlatMinusCoordinate Q b L n a).toFun := by
        rw [Fintype.sum_prod_type]
      _ = ∑ a : Fin 2 × Fin 2, primalEnergy U (Real.sqrt 3)
          (fun x => (uU.toFun x).ofLp a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [show (fun x => (uU.toFun x).ofLp a) =
          (mainFlatMinusCoordinate Q b L n a).toFun by rfl]
      _ = _ := hraw.symm
  have hmeanEq :
      (∑ i : Fin 2, blockVecDot
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))) =
      hilbertEnergy U (hilbertCubeIncrement U 0 uU.toFun) := by
    calc
      _ = ∑ a : Fin 2 × Fin 2,
          (cubeAverage U (fun x => (uU.toFun x).ofLp a)) ^ 2 := by
        calc
          _ = ∑ i : Fin 2, ∑ k : Fin 2,
                (cubeAverage U (fun x =>
                  (uU.toFun x).ofLp (i, k))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [oldSignedFlatMinusBlock, oldSignedBlockMean,
              blockVecDot, vecDot, Prod.fst, Prod.snd]
            have hcoordsum :
                (∑ k : Fin 2,
                  cubeAverage U (fun x =>
                    (mainFlatMinusCoordinate Q b L n (i, k)).toFun x) *
                  cubeAverage U (fun x =>
                    (mainFlatMinusCoordinate Q b L n (i, k)).toFun x)) =
                (∑ k : Fin 2,
                  cubeAverage U (fun x => (uU.toFun x).ofLp (i, k)) *
                  cubeAverage U (fun x => (uU.toFun x).ofLp (i, k))) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show (fun x => (uU.toFun x).ofLp (i, k)) =
                (mainFlatMinusCoordinate Q b L n (i, k)).toFun by rfl]
            rw [hcoordsum]
            simp [cubeAverage_const, pow_two]
          _ = _ := by rw [Fintype.sum_prod_type]
      _ = _ := hroot0.symm
  have hcircNonneg :
      0 ≤ hilbertPrimalCircEnergy U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) uU.toFun := by
    unfold hilbertPrimalCircEnergy
    apply tsum_nonneg
    intro k
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (hilbertEnergy_nonneg U _)
  calc
    _ = hilbertPrimalEnergy U (Real.sqrt 3) uU.toFun -
        hilbertEnergy U (hilbertCubeIncrement U 0 uU.toFun) := by
      rw [hcentered, hrawEq, hmeanEq]
    _ = hilbertPrimalCircEnergy U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) uU.toFun := by
      rw [← main_hilbert_flat_row_q3_eq_sqrt3_hotcopy]
      simp only [hilbertPrimalEnergy, hilbertPrimalCircEnergy]
      ring
    _ = hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        uU.toFun ^ 2 := by
      rw [hilbertPositiveCircHaarNorm, Real.sq_sqrt hcircNonneg]
    _ = _ := rfl


/-- Scale arithmetic: when the cell side `r` satisfies `3^6 r ≤ L`, the shell field
variance `σ²` obeys `r² σ² ≤ 31.2 A₂`. -/
theorem hot_flat_scale_arith (r b : ℝ) (L : {l : ℝ // 0 < l}) (hr : 0 < r)
    (hL : r * (3 : ℝ) ^ 6 ≤ L.1) :
    r ^ 2 * mainFlatSigmaSq b L ≤ (31.2 : ℝ) * mainA2 (b ^ 2) := by
  have hL0 := L.2
  have hrL : 0 < r * (3 : ℝ) ^ 6 := by positivity
  have hsq : (r * (3 : ℝ) ^ 6) ^ 2 ≤ L.1 ^ 2 := pow_le_pow_left₀ hrL.le hL 2
  unfold mainFlatSigmaSq mainA2
  have h1 : r ^ 2 * (2 * (b ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ))) ≤
      r ^ 2 * (2 * (b ^ 2 / (r * (3 : ℝ) ^ 6) ^ 2 * (78 / 5 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
    have : b ^ 2 / L.1 ^ 2 ≤ b ^ 2 / (r * (3 : ℝ) ^ 6) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg b) (by positivity) hsq
    nlinarith [this]
  refine h1.trans (le_of_eq ?_)
  field_simp
  norm_num [zpow_neg]
  ring

theorem main_hot_flatPlus_descendant_average_le_mainOp_sq
    (Q : TriadicCube 2) (depth : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : cubeScaleFactor Q / (3 : ℝ) ^ depth * (3 : ℝ) ^ 6 ≤ L.1) :
    descendantsAverage Q depth (fun U =>
      oldSignedFlatOscillationSize Q U b L true ^ 2) ≤ mainOp (b ^ 2) ^ 2 := by
  let q : ℝ := (3 : ℝ) ^ (2 * (1 / 4 : ℝ))
  let F : Gaussian.whiteBasisIndex → HilbertH1Function
      (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) := fun n =>
    mainFlatPlusH1 Q b L n
  let A : TriadicCube 2 → Gaussian.whiteBasisIndex → ℝ := fun U n =>
    hilbertPositiveCircHaarNorm U q (F n).toFun ^ 2
  let D : Gaussian.whiteBasisIndex → ℝ := fun n =>
    descendantsAverage Q depth (fun U => A U n)
  have hgrad := mainFlatPlusGradientEnergy_tsum Q b L
  have hDfull := main_hilbert_cell_circ_tsum_le_gradient Q depth F hgrad.1
  have hDseries := hDfull.1
  have hold_eq (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      oldSignedFlatOscillationSize Q U b L true ^ 2 = ∑' n, A U n := by
    change (Real.sqrt (∑' n : Gaussian.whiteBasisIndex, ∑ i : Fin 2,
      oldSignedBlockPositiveNorm U
        (oldSignedFlatInput Q b L true n i - fun _ =>
          oldSignedBlockMean U (oldSignedFlatInput Q b L true n i)) ^ 2)) ^ 2 = _
    have hnonneg : 0 ≤ ∑' n : Gaussian.whiteBasisIndex, ∑ i : Fin 2,
        oldSignedBlockPositiveNorm U
          (oldSignedFlatInput Q b L true n i - fun _ =>
            oldSignedBlockMean U (oldSignedFlatInput Q b L true n i)) ^ 2 := by
      apply tsum_nonneg
      intro n
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.sq_sqrt hnonneg]
    apply tsum_congr
    intro n
    simpa only [A, F, q, oldSignedFlatInput, ite_true] using
      main_oldSignedFlatPlus_mode_energy_eq_hilbertCirc_hotcopy Q U depth hU b L n
  have hAseries (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      Summable (fun n => A U n) := by
    have hraw := old_signed_flat_oscillation_budget_series Q depth b L true U hU
    apply hraw.congr
    intro n
    simpa only [A, F, q, oldSignedFlatInput, ite_true] using
      main_oldSignedFlatPlus_mode_energy_eq_hilbertCirc_hotcopy Q U depth hU b L n
  have hsumavg :
      (∑ U ∈ descendantsAtDepth Q depth,
        oldSignedFlatOscillationSize Q U b L true ^ 2) =
      (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n) := by
    apply Finset.sum_congr rfl
    intro U hU
    exact hold_eq U hU
  have hswap :
      (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n) =
        ∑' n, ∑ U ∈ descendantsAtDepth Q depth, A U n := by
    exact (Summable.tsum_finsetSum
      (fun U hU => hAseries U hU)).symm
  have haverage :
      descendantsAverage Q depth (fun U =>
        oldSignedFlatOscillationSize Q U b L true ^ 2) = ∑' n, D n := by
    calc
      _ = descendantsAverage Q depth (fun U => ∑' n, A U n) := by
        change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth,
              oldSignedFlatOscillationSize Q U b L true ^ 2) =
          ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n)
        exact congrArg (fun z : ℝ =>
          ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * z) hsumavg
      _ = ∑' n, D n := by
        change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n) =
          ∑' n, ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth, A U n)
        calc
          _ = ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
              (∑' n, ∑ U ∈ descendantsAtDepth Q depth, A U n) := by
            rw [hswap]
          _ = _ := by
            rw [← tsum_mul_left]
  have hr : 0 < cubeScaleFactor Q / (3 : ℝ) ^ depth :=
    div_pos (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q) (by positivity)
  have hscale := hot_flat_scale_arith (cubeScaleFactor Q / (3 : ℝ) ^ depth) b L hr hL
  have hc0 : planarC0 < 440 / 1000 := by
    have := ASDExplicitGamma.Triadic.planarC0_decimal_bounds.2
    norm_num at this ⊢
    linarith
  have hc00 : 0 ≤ planarC0 := by unfold planarC0; exact Real.sqrt_nonneg _
  have hOp : mainOp (b ^ 2) ^ 2 = (1 + Real.sqrt 2) ^ 2 * (440 / 1000) ^ 2 * ((156 / 5) * mainA2 (b ^ 2)) := by
    unfold mainOp
    have hA : 0 ≤ mainA2 (b ^ 2) := by unfold mainA2; positivity
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  calc
    _ = ∑' n, D n := haverage
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 *
        ∑' n, hilbertGradientEnergy Q (F n).grad := hDfull.2
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 * ((1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq b L) :=
        mul_le_mul_of_nonneg_left (hgrad.2) (sq_nonneg _)
    _ ≤ _ := by
      rw [hOp]
      have hc2 : planarC0 ^ 2 ≤ (440 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hc00 hc0.le 2
      have hmid : planarC0 ^ 2 * (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L ≤
          (440 / 1000 : ℝ) ^ 2 * ((156 / 5) * mainA2 (b ^ 2)) := by
        have h31 : (31.2 : ℝ) = 156 / 5 := by norm_num
        rw [h31] at hscale
        calc planarC0 ^ 2 * (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L
            = planarC0 ^ 2 * ((cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L) := by ring
          _ ≤ (440 / 1000 : ℝ) ^ 2 * ((156 / 5) * mainA2 (b ^ 2)) :=
              mul_le_mul hc2 hscale (by unfold mainFlatSigmaSq; positivity) (by positivity)
      have hf := mul_le_mul_of_nonneg_left hmid (sq_nonneg (1 + Real.sqrt 2))
      calc _ = (1 + Real.sqrt 2) ^ 2 * (planarC0 ^ 2 * (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L) := by ring
        _ ≤ _ := hf.trans (le_of_eq (by ring))

theorem main_hot_flatMinus_descendant_average_le_mainOm_sq
    (Q : TriadicCube 2) (depth : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : cubeScaleFactor Q / (3 : ℝ) ^ depth * (3 : ℝ) ^ 6 ≤ L.1) :
    descendantsAverage Q depth (fun U =>
      oldSignedFlatOscillationSize Q U b L false ^ 2) ≤ mainOm (b ^ 2) ^ 2 := by
  let q : ℝ := (3 : ℝ) ^ (2 * (1 / 4 : ℝ))
  let F : Gaussian.whiteBasisIndex → HilbertH1Function
      (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) := fun n =>
    mainFlatMinusH1 Q b L n
  let A : TriadicCube 2 → Gaussian.whiteBasisIndex → ℝ := fun U n =>
    hilbertPositiveCircHaarNorm U q (F n).toFun ^ 2
  let D : Gaussian.whiteBasisIndex → ℝ := fun n =>
    descendantsAverage Q depth (fun U => A U n)
  have hgrad := mainFlatMinusGradientEnergy_tsum Q b L
  have hDfull := main_hilbert_cell_circ_tsum_le_gradient Q depth F hgrad.1
  have hDseries := hDfull.1
  have hold_eq (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      oldSignedFlatOscillationSize Q U b L false ^ 2 = ∑' n, A U n := by
    change (Real.sqrt (∑' n : Gaussian.whiteBasisIndex, ∑ i : Fin 2,
      oldSignedBlockPositiveNorm U
        (oldSignedFlatInput Q b L false n i - fun _ =>
          oldSignedBlockMean U (oldSignedFlatInput Q b L false n i)) ^ 2)) ^ 2 = _
    have hnonneg : 0 ≤ ∑' n : Gaussian.whiteBasisIndex, ∑ i : Fin 2,
        oldSignedBlockPositiveNorm U
          (oldSignedFlatInput Q b L false n i - fun _ =>
            oldSignedBlockMean U (oldSignedFlatInput Q b L false n i)) ^ 2 := by
      apply tsum_nonneg
      intro n
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.sq_sqrt hnonneg]
    apply tsum_congr
    intro n
    simpa only [A, F, q, oldSignedFlatInput, Bool.false_eq_true, ite_false] using
      main_oldSignedFlatMinus_mode_energy_eq_hilbertCirc_hotcopy Q U depth hU b L n
  have hAseries (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      Summable (fun n => A U n) := by
    have hraw := old_signed_flat_oscillation_budget_series Q depth b L false U hU
    apply hraw.congr
    intro n
    simpa only [A, F, q, oldSignedFlatInput, Bool.false_eq_true, ite_false] using
      main_oldSignedFlatMinus_mode_energy_eq_hilbertCirc_hotcopy Q U depth hU b L n
  have hsumavg :
      (∑ U ∈ descendantsAtDepth Q depth,
        oldSignedFlatOscillationSize Q U b L false ^ 2) =
      (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n) := by
    apply Finset.sum_congr rfl
    intro U hU
    exact hold_eq U hU
  have hswap :
      (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n) =
        ∑' n, ∑ U ∈ descendantsAtDepth Q depth, A U n := by
    exact (Summable.tsum_finsetSum
      (fun U hU => hAseries U hU)).symm
  have haverage :
      descendantsAverage Q depth (fun U =>
        oldSignedFlatOscillationSize Q U b L false ^ 2) = ∑' n, D n := by
    calc
      _ = descendantsAverage Q depth (fun U => ∑' n, A U n) := by
        change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth,
              oldSignedFlatOscillationSize Q U b L false ^ 2) =
          ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n)
        exact congrArg (fun z : ℝ =>
          ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * z) hsumavg
      _ = ∑' n, D n := by
        change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth, ∑' n, A U n) =
          ∑' n, ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
            (∑ U ∈ descendantsAtDepth Q depth, A U n)
        calc
          _ = ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
              (∑' n, ∑ U ∈ descendantsAtDepth Q depth, A U n) := by
            rw [hswap]
          _ = _ := by
            rw [← tsum_mul_left]
  have hr : 0 < cubeScaleFactor Q / (3 : ℝ) ^ depth :=
    div_pos (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q) (by positivity)
  have hscale := hot_flat_scale_arith (cubeScaleFactor Q / (3 : ℝ) ^ depth) b L hr hL
  have hc0 : planarC0 < 440 / 1000 := by
    have := ASDExplicitGamma.Triadic.planarC0_decimal_bounds.2
    norm_num at this ⊢
    linarith
  have hc00 : 0 ≤ planarC0 := by unfold planarC0; exact Real.sqrt_nonneg _
  have hOp : mainOm (b ^ 2) ^ 2 = (440 / 1000) ^ 2 * ((156 / 5) * mainA2 (b ^ 2)) := by
    unfold mainOm
    have hA : 0 ≤ mainA2 (b ^ 2) := by unfold mainA2; positivity
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc
    _ = ∑' n, D n := haverage
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 *
        ∑' n, hilbertGradientEnergy Q (F n).grad := hDfull.2
    _ ≤ (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 * (mainFlatSigmaSq b L) :=
        mul_le_mul_of_nonneg_left (hgrad.2.le) (sq_nonneg _)
    _ ≤ _ := by
      rw [hOp]
      have hc2 : planarC0 ^ 2 ≤ (440 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hc00 hc0.le 2
      have hmid : planarC0 ^ 2 * (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L ≤
          (440 / 1000 : ℝ) ^ 2 * ((156 / 5) * mainA2 (b ^ 2)) := by
        have h31 : (31.2 : ℝ) = 156 / 5 := by norm_num
        rw [h31] at hscale
        calc planarC0 ^ 2 * (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L
            = planarC0 ^ 2 * ((cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L) := by ring
          _ ≤ (440 / 1000 : ℝ) ^ 2 * ((156 / 5) * mainA2 (b ^ 2)) :=
              mul_le_mul hc2 hscale (by unfold mainFlatSigmaSq; positivity) (by positivity)
      calc _ = planarC0 ^ 2 * (cubeScaleFactor Q / (3 : ℝ) ^ depth) ^ 2 * mainFlatSigmaSq b L := by ring
        _ ≤ _ := hmid

end
end ASDExplicitGamma.Main
