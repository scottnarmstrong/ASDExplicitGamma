module

public import ASDExplicitGamma.Main.EOscillationFlatOscillationCaps
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import ASDExplicitGamma.Native.OldSignedPartitionSeries

/-! Sharp mesh-scaled oscillation caps for the actual OLD flat rows.
The coordinate identities are adapted from EOScillationSourceFlatProfile;
the conclusion uses its generic gradient producer at the actual shell length. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

private theorem old_signed_flat_weight_sqrt3 :
    (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 := by
  rw [show 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow]

private theorem old_signed_flat_average_neg
    (U : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage U (fun x => -f x) = -cubeAverage U f := by
  unfold cubeAverage
  rw [integral_neg]
  ring

private theorem old_signed_flat_plus_mode_circ_eq
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
        old_signed_flat_weight_sqrt3.symm
  have hq9 : (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) < 9 := by
    calc
      (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 :=
        old_signed_flat_weight_sqrt3
      _ < 9 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
  have hseriesQ := (hilbert_positive_poincare_of_weight U hq hq9 uU).1
  have hseries : Summable (fun k => (Real.sqrt 3)^(k+1) *
      hilbertEnergy U (hilbertCubeIncrement U (k+1) uU.toFun)) := by
    simpa only [old_signed_flat_weight_sqrt3] using hseriesQ
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
              blockVecDot, vecDot]
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
              rw [old_signed_flat_average_neg,
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
      rw [← old_signed_flat_weight_sqrt3]
      simp only [hilbertPrimalEnergy, hilbertPrimalCircEnergy]
      ring
    _ = hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        uU.toFun ^ 2 := by
      rw [hilbertPositiveCircHaarNorm, Real.sq_sqrt hcircNonneg]
    _ = _ := rfl

private theorem old_signed_flat_minus_mode_circ_eq
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
        old_signed_flat_weight_sqrt3.symm
  have hq9 : (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) < 9 := by
    calc
      (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 :=
        old_signed_flat_weight_sqrt3
      _ < 9 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg 3]
  have hseriesQ := (hilbert_positive_poincare_of_weight U hq hq9 uU).1
  have hseries : Summable (fun k => (Real.sqrt 3)^(k+1) *
      hilbertEnergy U (hilbertCubeIncrement U (k+1) uU.toFun)) := by
    simpa only [old_signed_flat_weight_sqrt3] using hseriesQ
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
        simp [oldSignedFlatMinusBlock, old_signed_primal_zero]
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
              blockVecDot, vecDot]
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
      rw [← old_signed_flat_weight_sqrt3]
      simp only [hilbertPrimalEnergy, hilbertPrimalCircEnergy]
      ring
    _ = hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        uU.toFun ^ 2 := by
      rw [hilbertPositiveCircHaarNorm, Real.sq_sqrt hcircNonneg]
    _ = _ := rfl

/-- Complete plus oscillation, with the actual mesh length and full mode sum. -/
theorem old_signed_flat_plus_partition_oscillation_cap
    (Q : TriadicCube 2) (r : ℕ) (b : ℝ) (L : {l : ℝ // 0<l}) :
    descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)≤
      (cubeScaleFactor Q/(3:ℝ)^r*planarC0)^2*((1+Real.sqrt 2)^2*mainFlatSigmaSq b L) := by
  let q : ℝ := (3:ℝ)^(2*(1/4:ℝ))
  let F := fun n => mainFlatPlusH1 Q b L n
  let f := fun n U => hilbertPositiveCircHaarNorm U q (F n).toFun^2
  have hgrad := mainFlatPlusGradientEnergy_tsum Q b L
  have hp := main_hilbert_cell_circ_tsum_le_gradient Q r F hgrad.1
  have hmode (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) (n : whiteBasisIndex) :
      (∑ i : Fin 2,oldSignedBlockPositiveNorm U (oldSignedFlatInput Q b L true n i-
        fun _ => oldSignedBlockMean U (oldSignedFlatInput Q b L true n i))^2)=f n U := by
    simpa only [f,F,q,oldSignedFlatInput,ite_true] using
      old_signed_flat_plus_mode_circ_eq Q U r hU b L n
  have hs (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) : Summable (fun n => f n U) :=
    (old_signed_flat_oscillation_budget_series Q r b L true U hU).congr (hmode U hU)
  have he (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) :
      oldSignedFlatOscillationSize Q U b L true^2=∑' n,f n U := by
    rw [oldSignedFlatOscillationSize,Real.sq_sqrt (tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => sq_nonneg _)))]
    exact tsum_congr (hmode U hU)
  have hpart := old_signed_partition_series Q r f hs
  have heavg : descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2)=
      descendantsAverage Q r (fun U => ∑' n,f n U) := by
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    exact he
  rw [heavg,←hpart.2]
  exact hp.2.trans (mul_le_mul_of_nonneg_left (hgrad.2) (sq_nonneg _))

/-- Complete minus oscillation, with the actual mesh length and full mode sum. -/
theorem old_signed_flat_minus_partition_oscillation_cap
    (Q : TriadicCube 2) (r : ℕ) (b : ℝ) (L : {l : ℝ // 0<l}) :
    descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)≤
      (cubeScaleFactor Q/(3:ℝ)^r*planarC0)^2*(mainFlatSigmaSq b L) := by
  let q : ℝ := (3:ℝ)^(2*(1/4:ℝ))
  let F := fun n => mainFlatMinusH1 Q b L n
  let f := fun n U => hilbertPositiveCircHaarNorm U q (F n).toFun^2
  have hgrad := mainFlatMinusGradientEnergy_tsum Q b L
  have hp := main_hilbert_cell_circ_tsum_le_gradient Q r F hgrad.1
  have hmode (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) (n : whiteBasisIndex) :
      (∑ i : Fin 2,oldSignedBlockPositiveNorm U (oldSignedFlatInput Q b L false n i-
        fun _ => oldSignedBlockMean U (oldSignedFlatInput Q b L false n i))^2)=f n U := by
    simpa only [f,F,q,oldSignedFlatInput,Bool.false_eq_true,ite_false] using
      old_signed_flat_minus_mode_circ_eq Q U r hU b L n
  have hs (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) : Summable (fun n => f n U) :=
    (old_signed_flat_oscillation_budget_series Q r b L false U hU).congr (hmode U hU)
  have he (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r) :
      oldSignedFlatOscillationSize Q U b L false^2=∑' n,f n U := by
    rw [oldSignedFlatOscillationSize,Real.sq_sqrt (tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => sq_nonneg _)))]
    exact tsum_congr (hmode U hU)
  have hpart := old_signed_partition_series Q r f hs
  have heavg : descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2)=
      descendantsAverage Q r (fun U => ∑' n,f n U) := by
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    exact he
  rw [heavg,←hpart.2]
  exact hp.2.trans (mul_le_mul_of_nonneg_left (le_of_eq hgrad.2) (sq_nonneg _))

end
end ASDExplicitGamma.Native
