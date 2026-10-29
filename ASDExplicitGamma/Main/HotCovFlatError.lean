module

public import ASDExplicitGamma.Main.HotCovFlatMean
public import ASDExplicitGamma.Native.OldSignedFlatMeanLoss
public import ASDExplicitGamma.Native.OldSignedFlatCellRegularity
public import ASDExplicitGamma.Native.OldSignedFlatOscillationCaps

/-! MA-E-COVARIANCE, step 9 (NOTE (4.1)): the boundary-plus-oscillation bill of the
cell covariance error `E^±_U`, in both signs. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Scalar
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse

noncomputable section

/-- The cell mean of the signed native flat block is the signed coordinate mean. -/
theorem hotCov_block_mean_coordinate (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (U : TriadicCube 2) (n : whiteBasisIndex) (i k : Fin 2) :
    (if plus then (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)).2 k
      else (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)).1 k) =
      (if plus then -1 else 1) * hotCovFlatMean Q b L plus U n i k := by
  cases plus
  · simp [oldSignedBlockMean, oldSignedFlatInput, oldSignedFlatMinusBlock, hotCovFlatMean,
      oldSignedFlatCoordinate]
  · simp only [oldSignedBlockMean, oldSignedFlatInput, oldSignedFlatPlusBlock, hotCovFlatMean,
      oldSignedFlatCoordinate, if_true]
    have h : cubeAverage U (fun x => -mainFlatPlusCoordinate Q b L n (i, k) x) =
        -cubeAverage U (fun x => mainFlatPlusCoordinate Q b L n (i, k) x) := by
      unfold cubeAverage
      rw [integral_neg]
      ring
    simpa using h

/-- Parseval for the centered finite-parent flat kernel on a named source cell. -/
theorem hotCov_centered_kernel_hasSum (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    HasSum (fun j : whiteBasisIndex => energy U (fun x =>
      oldSignedFlatCoordinate Q b L plus j (i, k) x - hotCovFlatMean Q b L plus U j i k))
      (hilbertEnergy U (fun x => (hotCovFlatKernel Q b L plus i k).toFun x -
        hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)) := by
  let g := (hotCovFlatKernel Q b L plus i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  let G := (hotCovFlatKernel Q b L plus i k).toFun
  have hm : MemLp (fun x => G x - hilbertCubeAverage U G) 2 (normalizedCubeMeasure U) :=
    (g.memL2_normalized U).sub (memLp_const _)
  have he (j : whiteBasisIndex) : energy U (fun x => inner ℝ (whiteBasis j)
      (G x - hilbertCubeAverage U G)) = energy U (fun x =>
      oldSignedFlatCoordinate Q b L plus j (i, k) x - hotCovFlatMean Q b L plus U j i k) := by
    rw [energy_eq_integral_sq, energy_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [hotCov_flat_kernel_coefficient Q depth b L plus U hU i k j] with x hx
    rw [inner_sub_right, hx, hotCov_flat_kernel_mean Q depth b L plus U hU i k j]
  rw [hilbertEnergy_eq_tsum_coordinates U whiteBasis hm]
  exact (hilbertEnergy_coordinates_summable U whiteBasis whiteBasis.orthonormal hm).hasSum.congr_fun
    (fun j => (he j).symm)

theorem hotCov_centered_mode_positive (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (j : whiteBasisIndex) (i : Fin 2) :
    (∑ k : Fin 2, energy U (fun x =>
      oldSignedFlatCoordinate Q b L plus j (i, k) x - hotCovFlatMean Q b L plus U j i k)) ≤
      oldSignedBlockPositiveNorm U (oldSignedFlatInput Q b L plus j i -
        fun _ => oldSignedBlockMean U (oldSignedFlatInput Q b L plus j i)) ^ 2 := by
  let F := oldSignedFlatInput Q b L plus j i
  let m := oldSignedBlockMean U F
  let Fc := F - fun _ => m
  have hF : MemBlockL2 (openCubeSet U) F :=
    old_signed_flat_input_cell_memL2 Q depth b L plus j i U hU
  have hFc : MemBlockL2 (openCubeSet U) Fc := hF.sub (memLp_const m)
  have hp := old_signed_block_l2_le_positive U Fc hFc
    (fun k => by
      simpa only [Fc, F, Pi.sub_apply, Prod.fst_sub] using
        old_signed_flat_input_cell_first_positive Q depth b L plus j i U hU m.1 k)
    (fun k => by
      simpa only [Fc, F, Pi.sub_apply, Prod.snd_sub] using
        old_signed_flat_input_cell_second_positive Q depth b L plus j i U hU m.2 k)
  have hmean := hotCov_block_mean_coordinate Q b L plus U j i
  cases plus
  · have hh : (∑ k : Fin 2, energy U (fun x =>
        oldSignedFlatCoordinate Q b L false j (i, k) x - hotCovFlatMean Q b L false U j i k)) ≤
        oldSignedBlockL2Energy U Fc := by
      have e1 : (∑ k : Fin 2, energy U (fun x => (F x).1 k - m.1 k)) =
          ∑ k : Fin 2, energy U (fun x =>
            oldSignedFlatCoordinate Q b L false j (i, k) x - hotCovFlatMean Q b L false U j i k) := by
        apply Finset.sum_congr rfl
        intro k _
        have := hmean k
        simp only [Bool.false_eq_true, if_false, one_mul] at this
        simp only [F, m, oldSignedFlatInput, Bool.false_eq_true, if_false, oldSignedFlatMinusBlock,
          oldSignedFlatCoordinate, this]
        rfl
      rw [← e1]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => energy_nonneg U _))
    exact hh.trans hp
  · have hh : (∑ k : Fin 2, energy U (fun x =>
        oldSignedFlatCoordinate Q b L true j (i, k) x - hotCovFlatMean Q b L true U j i k)) ≤
        oldSignedBlockL2Energy U Fc := by
      have e1 : (∑ k : Fin 2, energy U (fun x => (F x).2 k - m.2 k)) =
          ∑ k : Fin 2, energy U (fun x =>
            oldSignedFlatCoordinate Q b L true j (i, k) x - hotCovFlatMean Q b L true U j i k) := by
        apply Finset.sum_congr rfl
        intro k _
        have := hmean k
        simp only [if_true, neg_mul, one_mul] at this
        have hfun : (fun x => (F x).2 k - m.2 k) = fun x => -(
            oldSignedFlatCoordinate Q b L true j (i, k) x -
              hotCovFlatMean Q b L true U j i k) := by
          funext x
          simp only [F, oldSignedFlatInput, if_true, oldSignedFlatPlusBlock,
            oldSignedFlatCoordinate]
          have h2 : m.2 k = -hotCovFlatMean Q b L true U j i k := this
          rw [h2]
          ring
        rw [hfun, energy_neg]
      rw [← e1]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun k _ => energy_nonneg U _))
    exact hh.trans hp

/-- The complete centered flat kernel (all four outputs) costs the actual joint
oscillation size, with no load or mode-count factor. -/
theorem hotCov_centered_kernel_energy (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) :
    (∑ i : Fin 2, ∑ k : Fin 2, hilbertEnergy U (fun x =>
      (hotCovFlatKernel Q b L plus i k).toFun x -
        hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)) ≤
      oldSignedFlatOscillationSize Q U b L plus ^ 2 := by
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun k _ =>
      hotCov_centered_kernel_hasSum Q depth b L plus U hU i k))
  rw [← hs.tsum_eq]
  rw [oldSignedFlatOscillationSize, Real.sq_sqrt (tsum_nonneg (fun j =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _)))]
  apply hs.summable.tsum_le_tsum _ (old_signed_flat_oscillation_budget_series Q depth b L plus U hU)
  intro j
  exact Finset.sum_le_sum (fun i _ => hotCov_centered_mode_positive Q depth b L plus U hU j i)

theorem hotCov_meanCov_error_entry_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    let F := q3Section b L h3Zero
    let G := (hotCovFlatKernel Q b L plus i k).toFun
    |hotCovMeanCovErr Q U b L plus k i| ≤
      |b| * Real.sqrt (hilbertEnergy U (oldSignedRemainderKernel Q b L plus (i, k)).toFun) +
        Real.sqrt (hilbertEnergy U (fun x => F x - hilbertCubeAverage U F)) *
          Real.sqrt (hilbertEnergy U (fun x => G x - hilbertCubeAverage U G)) := by
  intro F G
  let g := (hotCovFlatKernel Q b L plus i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  let R := (oldSignedRemainderKernel Q b L plus (i, k)).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  have hF : MemLp F 2 (normalizedCubeMeasure U) := old_hessian_white_section_memLp U b L
  have hG : MemLp G 2 (normalizedCubeMeasure U) := g.memL2_normalized U
  have hR : MemLp R.toFun 2 (normalizedCubeMeasure U) := R.memL2_normalized U
  have hb := old_hessian_hilbert_pairing_cauchy U F R.toFun hF hR
  rw [old_hessian_white_section_energy, Real.sqrt_sq_eq_abs] at hb
  have hc := old_hessian_hilbert_pairing_cauchy U
    (fun x => F x - hilbertCubeAverage U F) (fun x => G x - hilbertCubeAverage U G)
    (hF.sub (memLp_const _)) (hG.sub (memLp_const _))
  rw [hotCov_meanCov_error_identity Q depth b L plus U hU i k]
  exact (abs_sub _ _).trans (add_le_add hb hc)

/-- The actual deterministic two-load covariance-error energy on one cell. -/
def hotCovErrCellEnergy (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) : ℝ :=
  ∑ i : Fin 2, ∑ k : Fin 2, (hotCovMeanCovErr Q U b L plus k i) ^ 2

/-- Joint four-coordinate bill on one cell, without a coordinate-count loss. -/
theorem hotCov_err_cell_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) :
    Real.sqrt (hotCovErrCellEnergy Q U b L plus) ≤
      |b| * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2,
        hilbertEnergy U (oldSignedRemainderKernel Q b L plus (i, k)).toFun) +
      (cubeScaleFactor U / Real.pi) * Real.sqrt (mainFlatSigmaSq b L) *
        Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2, hilbertEnergy U (fun x =>
          (hotCovFlatKernel Q b L plus i k).toFun x -
            hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)) := by
  let C := (cubeScaleFactor U / Real.pi) * Real.sqrt (mainFlatSigmaSq b L)
  have hC : 0 ≤ C := mul_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' U).le Real.pi_pos.le)
    (Real.sqrt_nonneg _)
  have hv := Real.sqrt_le_sqrt (old_hessian_white_mean_variance U b L)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
    (div_nonneg (Triadic.cubeScaleFactor_pos' U).le Real.pi_pos.le)] at hv
  have hh := old_signed_finite_sqrt_energy_bound
    (fun a : Fin 2 × Fin 2 => hilbertEnergy U (oldSignedRemainderKernel Q b L plus a).toFun)
    (fun a : Fin 2 × Fin 2 => hilbertEnergy U (fun x =>
      (hotCovFlatKernel Q b L plus a.1 a.2).toFun x -
        hilbertCubeAverage U (hotCovFlatKernel Q b L plus a.1 a.2).toFun))
    (fun a : Fin 2 × Fin 2 => |hotCovMeanCovErr Q U b L plus a.2 a.1|)
    (abs_nonneg b) hC (fun a => hilbertEnergy_nonneg U _) (fun a => hilbertEnergy_nonneg U _)
    (fun a => abs_nonneg _) (fun a =>
      (hotCov_meanCov_error_entry_bound Q depth b L plus U hU a.1 a.2).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hv (Real.sqrt_nonneg _))))
  simpa only [hotCovErrCellEnergy, Fintype.sum_prod_type, sq_abs] using hh

/-- The harmonic kernel energy partitions to precisely half `Bflat`. -/
theorem hotCov_boundary_kernel_partition (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) :
    descendantsAverage Q depth (fun U => ∑ i : Fin 2, ∑ k : Fin 2,
      hilbertEnergy U (oldSignedRemainderKernel Q b L plus (i, k)).toFun) =
        oldSignedFlatBoundaryEnergy Q b L / 2 := by
  calc
    _ = ∑ i : Fin 2, ∑ k : Fin 2, hilbertEnergy Q
        (oldSignedRemainderKernel Q b L plus (i, k)).toFun := by
      simp_rw [Homogenization.descendantsAverage_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact (hilbertEnergy_eq_descendantsAverage Q depth
        ((oldSignedRemainderKernel Q b L plus (i, k)).memL2_normalized Q)).symm
    _ = _ := by simpa only [Fintype.sum_prod_type] using old_signed_remainder_kernel_energy Q b L plus

/-- The cell-averaged covariance error: boundary plus oscillation, jointly in all four
coordinates. -/
theorem hotCov_err_frobenius (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) :
    Real.sqrt (descendantsAverage Q depth (fun U => hotCovErrCellEnergy Q U b L plus)) ≤
      |b| * Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) +
      (cubeScaleFactor Q / (3 : ℝ) ^ depth / Real.pi) * Real.sqrt (mainFlatSigmaSq b L) *
        Real.sqrt (descendantsAverage Q depth (fun U =>
          oldSignedFlatOscillationSize Q U b L plus ^ 2)) := by
  let E := fun U => ∑ i : Fin 2, ∑ k : Fin 2,
    hilbertEnergy U (oldSignedRemainderKernel Q b L plus (i, k)).toFun
  let G := fun U => ∑ i : Fin 2, ∑ k : Fin 2, hilbertEnergy U (fun x =>
    (hotCovFlatKernel Q b L plus i k).toFun x -
      hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)
  let c := fun U => Real.sqrt (hotCovErrCellEnergy Q U b L plus)
  let C := (cubeScaleFactor Q / (3 : ℝ) ^ depth / Real.pi) * Real.sqrt (mainFlatSigmaSq b L)
  have hC : 0 ≤ C := mul_nonneg
    (div_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) depth)) Real.pi_pos.le)
    (Real.sqrt_nonneg _)
  have hc (U : TriadicCube 2) : 0 ≤ hotCovErrCellEnergy Q U b L plus :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hh := old_signed_descendant_sqrt_energy_bound Q depth E G c (abs_nonneg b) hC
    (fun U _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg U _)))
    (fun U _ => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg U _)))
    (fun U _ => Real.sqrt_nonneg _) (fun U hU => by
      have ht := hotCov_err_cell_bound Q depth b L plus U hU
      rw [cubeScaleFactor_descendant_eq_div_pow hU] at ht
      exact ht)
  simp only [c, Real.sq_sqrt (hc _)] at hh
  rw [hotCov_boundary_kernel_partition] at hh
  have hg : descendantsAverage Q depth G ≤
      descendantsAverage Q depth (fun U => oldSignedFlatOscillationSize Q U b L plus ^ 2) :=
    descendantsAverage_le (fun U hU => hotCov_centered_kernel_energy Q depth b L plus U hU)
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) hC))

end

end ASDExplicitGamma.Main
