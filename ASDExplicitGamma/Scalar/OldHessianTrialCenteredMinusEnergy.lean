module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenErrorIdentity
public import ASDExplicitGamma.Native.OldSignedFlatMeanLoss

/-! The complete centered finite-parent minus kernel is paid by the same
actual fine oscillation profile; no load or white-mode count is inserted. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Parseval for the actual centered minus kernel on a named source cell. -/
theorem old_hessian_centered_minus_kernel_hasSum (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    HasSum (fun j : whiteBasisIndex => energy U (fun x =>
      (oldSignedFlatMinusBlock Q b L j i x).1 k-
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k))
      (hilbertEnergy U (fun x => (oldHessianMinusKernel Q b L i k).toFun x-
        hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)) := by
  let g := (oldHessianMinusKernel Q b L i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  let G := (oldHessianMinusKernel Q b L i k).toFun
  have hm : MemLp (fun x => G x-hilbertCubeAverage U G) 2 (normalizedCubeMeasure U) :=
    (g.memL2_normalized U).sub (memLp_const _)
  have he (j : whiteBasisIndex) : energy U (fun x => inner ℝ (whiteBasis j)
      (G x-hilbertCubeAverage U G))=energy U (fun x =>
      (oldSignedFlatMinusBlock Q b L j i x).1 k-
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k) := by
    rw [energy_eq_integral_sq,energy_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [old_hessian_minus_kernel_coefficient Q depth b L U hU i k j] with x hx
    rw [inner_sub_right,hx,old_hessian_minus_kernel_mean Q depth b L U hU i k j]
  rw [hilbertEnergy_eq_tsum_coordinates U whiteBasis hm]
  exact (hilbertEnergy_coordinates_summable U whiteBasis whiteBasis.orthonormal hm).hasSum.congr_fun
    (fun j => (he j).symm)

/-- One centered mode's first energy is below its genuine block positive
energy, with all positive-series regularity proved from the actual flat H1 field. -/
theorem old_hessian_centered_minus_mode_positive (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (j : whiteBasisIndex) (i : Fin 2) :
    (∑ k : Fin 2,energy U (fun x => (oldSignedFlatMinusBlock Q b L j i x).1 k-
      (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k)) ≤
      oldSignedBlockPositiveNorm U (oldSignedFlatMinusBlock Q b L j i-
        fun _ => oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i))^2 := by
  let F := oldSignedFlatMinusBlock Q b L j i
  let m := oldSignedBlockMean U F
  let Fc := F-fun _ => m
  have hF : MemBlockL2 (openCubeSet U) F :=
    old_signed_flat_input_cell_memL2 Q depth b L false j i U hU
  have hFc : MemBlockL2 (openCubeSet U) Fc := hF.sub (memLp_const m)
  have hp := old_signed_block_l2_le_positive U Fc hFc
    (fun k => by simpa only [Fc,F,Pi.sub_apply,Prod.fst_sub,oldSignedFlatInput,Bool.false_eq_true,ite_false]
      using old_signed_flat_input_cell_first_positive Q depth b L false j i U hU m.1 k)
    (fun k => by simpa only [Fc,F,Pi.sub_apply,Prod.snd_sub,oldSignedFlatInput,Bool.false_eq_true,ite_false]
      using old_signed_flat_input_cell_second_positive Q depth b L false j i U hU m.2 k)
  have hh : (∑ k : Fin 2,energy U (fun x => (F x).1 k-m.1 k))≤oldSignedBlockL2Energy U Fc :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => energy_nonneg U _))
  exact hh.trans hp

/-- The two-load/four-output complete centered kernel energy costs the
same actual OmegaMinus square, without an extra factor of two. -/
theorem old_hessian_centered_minus_kernel_energy (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) :
    (∑ i : Fin 2,∑ k : Fin 2,hilbertEnergy U (fun x => (oldHessianMinusKernel Q b L i k).toFun x-
      hilbertCubeAverage U (oldHessianMinusKernel Q b L i k).toFun)) ≤
        oldSignedFlatOscillationSize Q U b L false^2 := by
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun k _ =>
      old_hessian_centered_minus_kernel_hasSum Q depth b L U hU i k))
  rw [←hs.tsum_eq]
  rw [oldSignedFlatOscillationSize,Real.sq_sqrt (tsum_nonneg (fun j =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _)))]
  apply hs.summable.tsum_le_tsum _ (old_signed_flat_oscillation_budget_series Q depth b L false U hU)
  intro j
  exact Finset.sum_le_sum (fun i _ => old_hessian_centered_minus_mode_positive Q depth b L U hU j i)

end
end ASDExplicitGamma.Scalar
