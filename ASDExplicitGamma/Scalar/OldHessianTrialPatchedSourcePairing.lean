module

public import ASDExplicitGamma.Scalar.OldHessianTrialResidualSourceCross
public import ASDExplicitGamma.Native.OldSignedEnergyPartition

/-! Actual source/Z pairing on the unchanged fine partition. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The source stays unchanged while the genuine patched receiver is
restricted to each original fine cell. -/
theorem old_hessian_patched_source_pairing (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k F (oldSignedLocalResidual Q fine nu sigma hnu hsigma k G hG)=
      oldSignedCellAverage Q fine (fun U => oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) F
        (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k G hG)) := by
  rw [old_signed_energy_pairing_partition Q fine nu sigma hnu hsigma k hF
    (old_signed_local_residual_memLp Q fine nu sigma hnu hsigma k G hG)]
  apply congrArg (oldSignedCellAverage Q fine)
  funext U
  exact old_signed_energy_pairing_congr_ae U.val nu sigma _ Filter.EventuallyEq.rfl
    (old_signed_local_residual_restrict Q fine nu sigma hnu hsigma k G hG U.val U.property)

/-- The actual full mixed residual/Z cross partitions with exactly the
same source and original flat minus receiver; all projections are genuine. -/
theorem old_hessian_actual_source_pairing_partition (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedEnergyPairing Q nu sigma k
      (oldHessianMixedBottomResidual Q coarse fine nu sigma hnu hsigma k b L n i)
      (oldSignedPatchedMinus Q fine nu sigma hnu hsigma k b L n i)=
    oldSignedCellAverage Q fine (fun U => oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L n i)
      (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L n i) (old_signed_flat_minus_block_memL2 Q b L n i))) := by
  rw [old_hessian_actual_residual_source_cross]
  exact old_hessian_patched_source_pairing Q fine nu sigma hnu hsigma k _ _
    (old_hessian_mixed_bottom_source_memL2 Q coarse fine nu sigma hnu hsigma k b L n i)
    (old_signed_flat_minus_block_memL2 Q b L n i)

end
end ASDExplicitGamma.Scalar
