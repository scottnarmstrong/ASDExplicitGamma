module

public import ASDExplicitGamma.Native.OldSignedFlatMeanLoss
public import ASDExplicitGamma.Main.FlatFieldCellGeometry
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates

/-! Exact coordinate variance identities for the physical OLD flat modes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main
noncomputable section

/-- Coordinate variance of a finite Hilbert field is the corresponding
physical scalar L2 energy minus its mean square. -/
theorem old_signed_hilbert_variance_coordinates {I : Type*} [Fintype I]
    (U : TriadicCube 2) (F : Vec 2 → EuclideanSpace ℝ I)
    (hF : MemLp F 2 (normalizedCubeMeasure U)) :
    hilbertEnergy U (fun x => F x-hilbertCubeAverage U F)=
      ∑ i, (energy U (fun x => (F x).ofLp i)-cubeAverage U (fun x => (F x).ofLp i)^2) := by
  have hmean (i : I) : (hilbertCubeAverage U F).ofLp i=cubeAverage U (fun x => (F x).ofLp i) := by
    have hh := hilbertCubeAverage_map U (PiLp.proj 2 (fun _ : I => ℝ) i) hF
    simpa only [hilbertCubeAverage_real,PiLp.proj_apply] using hh.symm
  have hcenter : MemLp (fun x => F x-hilbertCubeAverage U F) 2 (normalizedCubeMeasure U) :=
    hF.sub (memLp_const _)
  rw [main_hilbertEnergy_euclidean U hcenter]
  apply Finset.sum_congr rfl
  intro i _
  have hfi : MemLp (fun x => (F x).ofLp i) 2 (normalizedCubeMeasure U) := by
    let pr : EuclideanSpace ℝ I →L[ℝ] ℝ := PiLp.proj 2 (fun _ : I => ℝ) i
    exact pr.comp_memLp' hF
  change energy U (fun x => (F x).ofLp i-(hilbertCubeAverage U F).ofLp i)=_
  rw [hmean,energy_sub U hfi (memLp_const _),pairing_const_right,energy_const]
  ring

private theorem average_neg (U : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage U (fun x => -f x)=-cubeAverage U f := by
  unfold cubeAverage
  rw [integral_neg]
  ring

/-- Restricting the actual plus Hilbert mode keeps its four scalar
coordinates in normalized L2 on each comparison cell. -/
theorem old_signed_flat_plus_hilbert_cell_L2 (Q : TriadicCube 2) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    MemLp (mainFlatPlusH1 Q b L n).toFun 2 (normalizedCubeMeasure U) := by
  let u := (mainFlatPlusH1 Q b L n).restrict (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    (measurableSet_openCubeSet Q)
  exact u.memL2_normalized U

/-- The analogous actual minus Hilbert mode has the same cell restriction. -/
theorem old_signed_flat_minus_hilbert_cell_L2 (Q : TriadicCube 2) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    MemLp (mainFlatMinusH1 Q b L n).toFun 2 (normalizedCubeMeasure U) := by
  let u := (mainFlatMinusH1 Q b L n).restrict (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    (measurableSet_openCubeSet Q)
  exact u.memL2_normalized U

/-- Exact complete-column plus cell variance, including its harmless sign
in the doubled physical flat block. -/
theorem old_signed_flat_plus_mode_variance (Q : TriadicCube 2) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2, (oldSignedBlockL2Energy U (oldSignedFlatInput Q b L true n i)-
      blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L true n i))
        (oldSignedBlockMean U (oldSignedFlatInput Q b L true n i))))=
      hilbertEnergy U (fun x => (mainFlatPlusH1 Q b L n).toFun x-
        hilbertCubeAverage U (mainFlatPlusH1 Q b L n).toFun) := by
  rw [old_signed_hilbert_variance_coordinates U _ (old_signed_flat_plus_hilbert_cell_L2 Q r U hU b L n),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [oldSignedFlatInput,ite_true,oldSignedBlockL2Energy,oldSignedFlatPlusBlock,
    oldSignedBlockMean,blockVecDot,vecDot,Pi.zero_apply,energy_const,zero_pow (by decide : 2≠0),
    Finset.sum_const_zero,zero_add,energy_neg,cubeAverage_const,mul_zero,average_neg,neg_mul_neg]
  rw [←Finset.sum_sub_distrib]
  simp only [pow_two]
  rfl

/-- Exact complete-column minus cell variance on the same tiling. -/
theorem old_signed_flat_minus_mode_variance (Q : TriadicCube 2) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q r)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2, (oldSignedBlockL2Energy U (oldSignedFlatInput Q b L false n i)-
      blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L false n i))
        (oldSignedBlockMean U (oldSignedFlatInput Q b L false n i))))=
      hilbertEnergy U (fun x => (mainFlatMinusH1 Q b L n).toFun x-
        hilbertCubeAverage U (mainFlatMinusH1 Q b L n).toFun) := by
  rw [old_signed_hilbert_variance_coordinates U _ (old_signed_flat_minus_hilbert_cell_L2 Q r U hU b L n),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,oldSignedBlockL2Energy,oldSignedFlatMinusBlock,
    oldSignedBlockMean,blockVecDot,vecDot,Pi.zero_apply,energy_const,zero_pow (by decide : 2≠0),
    Finset.sum_const_zero,add_zero,cubeAverage_const,mul_zero]
  rw [←Finset.sum_sub_distrib]
  simp only [pow_two]
  rfl

end
end ASDExplicitGamma.Native
