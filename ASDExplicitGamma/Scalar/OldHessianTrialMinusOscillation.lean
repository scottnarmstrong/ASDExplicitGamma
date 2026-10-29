module

public import ASDExplicitGamma.Scalar.OldHessianTrialMatrixHistoryControl
public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy
public import ASDExplicitGamma.Native.OldSignedActualCellPotentials

/-! The genuine centered minus reciprocal receiver, on each original fine cell. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Reciprocal residual of the original minus mode after removing its own
cell mean. The projection and fine cell are unchanged. -/
def oldHessianMinusOscillationColumn (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) : Vec 2 → Vec 2 :=
  let kU := oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k
  let F := oldSignedFlatInput Q b L false p.1 p.2
  let G := fun x => F x-oldSignedBlockMean U.val F
  let hG : MemBlockL2 (openCubeSet U.val) G :=
    (old_signed_flat_input_cell_memL2 Q fine b L false p.1 p.2 U.val U.property).sub (memLp_const _)
  let Z := scalarResidualField U.val nu sigma hnu hsigma kU (toHilbertBlockL2OfBlockField hG)
  fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) Z x).2

/-- Every actual receiver coordinate belongs to the normalized cell L2 space. -/
theorem old_hessian_minus_oscillation_column_memLp (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) (i : Fin 2) :
    MemLp (fun x => oldHessianMinusOscillationColumn Q fine nu sigma hnu hsigma k b L p U x i)
      2 (normalizedCubeMeasure U.val) := by
  let kU := oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
    nu sigma hnu hsigma kU
  exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
    (memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 U.val _ hEll (Lp.memLp _))) i)

/-- The centered receiver pays precisely inverse history times response
history times its original positive oscillation energy. -/
theorem old_hessian_minus_oscillation_column_energy (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) :
    let a := responseFramePlanarCoefficientField nu sigma k
    vectorWeakHaarEnergy U.val (oldHessianMinusOscillationColumn Q fine nu sigma hnu hsigma k b L p U)≤
      (oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a)*
        oldSignedBlockPositiveNorm U.val (fun x => oldSignedFlatInput Q b L false p.1 p.2 x-
          oldSignedBlockMean U.val (oldSignedFlatInput Q b L false p.1 p.2))^2 := by
  intro a
  let kU := oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k
  let F := oldSignedFlatInput Q b L false p.1 p.2
  let G := fun x => F x-oldSignedBlockMean U.val F
  have hG : MemBlockL2 (openCubeSet U.val) G :=
    (old_signed_flat_input_cell_memL2 Q fine b L false p.1 p.2 U.val U.property).sub (memLp_const _)
  have he := old_signed_residual_reciprocal_weak_energy U.val nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hG)
  have hs := old_signed_flat_source_energy U.val nu sigma hnu hsigma kU G hG
    (old_signed_flat_input_cell_first_positive Q fine b L false p.1 p.2 U.val U.property _)
    (old_signed_flat_input_cell_second_positive Q fine b L false p.1 p.2 U.val U.property _)
  have hB : 0≤oldSignedInverseHistory U.val (responseFramePlanarCoefficientField nu sigma kU) :=
    lemmaVInverseHistory_nonneg U.val _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hh := he.trans (mul_le_mul_of_nonneg_left hs hB)
  have hc := old_signed_cell_histories Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
    nu sigma hnu hsigma k
  rw [hc.1,hc.2.1] at hh
  exact hh.trans_eq (mul_assoc _ _ _).symm

end
end ASDExplicitGamma.Scalar
