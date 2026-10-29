module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellResponse
public import ASDExplicitGamma.Scalar.OldHessianTrialPatchDrop
public import ASDExplicitGamma.Native.OldSignedEnergyPartition

/-! Exact partition of the actual coarse comparison energy. The first and
reciprocal components retain a single physical energy budget on every cell. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The globally patched comparison restricts to the actual difference of
parent and cell minimizers, rather than a new affine replacement. -/
theorem old_hessian_patch_comparison_restrict (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (D : OldSignedCellIndex Q depth) :
    (fun x => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x-
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x) =ᵐ[
        volumeMeasureOn (openCubeSet D.val)]
      (oldHessianParentCellComparison Q D.val
        (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P).eval := by
  have hh := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P) D.val D.property
  rw [old_signed_affine_cell_residual] at hh
  filter_upwards [hh] with x hx
  rw [hx]
  rfl

/-- The actual coarse patch drop is exactly the normalized sum of its local
homogeneous comparison energies. -/
theorem old_hessian_patch_drop_cell_partition (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldHessianPatchDrop Q depth nu sigma hnu hsigma k P =
      oldSignedCellAverage Q depth (fun D => oldSignedEnergyPairing D.val nu sigma
        (oldSignedCellCoefficient Q D.val
          (openCubeSet_subset_of_mem_descendantsAtDepth D.property) k)
        (oldHessianParentCellComparison Q D.val
          (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P).eval
        (oldHessianParentCellComparison Q D.val
          (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P).eval) := by
  have hmem := (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)).sub
    (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P))
  unfold oldHessianPatchDrop
  rw [old_signed_energy_pairing_partition Q depth nu sigma hnu hsigma k hmem hmem]
  congr 1
  funext D
  exact old_signed_energy_pairing_congr_ae D.val nu sigma _
    (old_hessian_patch_comparison_restrict Q depth nu sigma hnu hsigma k P D)
    (old_hessian_patch_comparison_restrict Q depth nu sigma hnu hsigma k P D)

/-- The cell energy in its genuine restricted coefficient equals the
same normalized physical pairing in the parent coefficient. -/
theorem old_hessian_cell_energy_parent_coefficient (Q D : TriadicCube 2)
    (hD : openCubeSet D ⊆ openCubeSet Q) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (W : BlockState 2) :
    oldSignedEnergyPairing D nu sigma (oldSignedCellCoefficient Q D hD k) W.eval W.eval =
      blockPairingAverage (openCubeSet D) (responseFramePlanarCoefficientField nu sigma k) W W := by
  unfold oldSignedEnergyPairing blockPairingAverage volumeAverage blockPairingIntegrand
  congr 1
  apply integral_congr_ae
  filter_upwards [old_signed_cell_frame_coefficient_ae Q D hD nu sigma k] with x hx
  simp only [blockCoeffField,←hx]

/-- The partition also holds directly in the parent physical coefficient. -/
theorem old_hessian_patch_drop_parent_partition (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldHessianPatchDrop Q depth nu sigma hnu hsigma k P =
      oldSignedCellAverage Q depth (fun D =>
        let W := oldHessianParentCellComparison Q D.val
          (openCubeSet_subset_of_mem_descendantsAtDepth D.property) nu sigma hnu hsigma k P
        blockPairingAverage (openCubeSet D.val) (responseFramePlanarCoefficientField nu sigma k) W W) := by
  rw [old_hessian_patch_drop_cell_partition]
  congr 1
  funext D
  exact old_hessian_cell_energy_parent_coefficient Q D.val _ nu sigma k _

/-- The cell comparison's paired weak estimate is in the original parent
coefficient, with its one local physical energy, before any bank maximum. -/
theorem old_hessian_parent_cell_paired_weak (Q D : TriadicCube 2)
    (hD : openCubeSet D ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let W := oldHessianParentCellComparison Q D hD nu sigma hnu hsigma k P
    vectorWeakHaarEnergy D W.potential+
      vectorWeakHaarEnergy D (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) ≤
        lemmaVInverseHistory D a ((3:ℝ)^(1/4:ℝ))*
          blockPairingAverage (openCubeSet D) a W W := by
  exact old_hessian_paired_response_weak D
    ((responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k).mono (measurableSet_openCubeSet D) hD) _
    (old_hessian_parent_cell_comparison_response Q D hD nu sigma hnu hsigma k P)
    (old_hessian_parent_cell_comparison_memL2 Q D hD nu sigma hnu hsigma k P)

/-- Tiling a genuine response retains the paired energy budget under one
common bound for the actual descendant histories. -/
theorem old_hessian_paired_response_tiled_weak (Q : TriadicCube 2) (depth : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hW : BlockResponseSpace a (openCubeSet Q) W)
    (hmem : MemBlockL2 (openCubeSet Q) W.eval) (B : ℝ)
    (hB : ∀ U ∈ descendantsAtDepth Q depth,
      lemmaVInverseHistory U a ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    lemmaVTiledWeakEnergy Q depth W.potential+
      lemmaVTiledWeakEnergy Q depth (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) ≤
        B*blockPairingAverage (openCubeSet Q) a W W := by
  unfold lemmaVTiledWeakEnergy
  rw [←descendantsAverage_add]
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      vectorWeakHaarEnergy U W.potential+
        vectorWeakHaarEnergy U (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) ≤
          B*blockPairingAverage (openCubeSet U) a W W := by
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let hEU := hEll.mono (measurableSet_openCubeSet U) hsub
    exact (old_hessian_paired_response_weak U hEU W
      (blockResponseSpace_restrict_subcube Q U hsub a hEll W hW hmem)
      (hmem.mono_measure (Measure.restrict_mono_set volume hsub))).trans
      (mul_le_mul_of_nonneg_right (hB U hU) (compatible_blockPairingAverage_nonneg hEU W))
  have hh := descendantsAverage_le hlocal
  rw [descendantsAverage_mul_left] at hh
  have he : descendantsAverage Q depth (fun U => blockPairingAverage (openCubeSet U) a W W)=
      blockPairingAverage (openCubeSet Q) a W W := by
    change descendantsAverage Q depth (fun U => integralAverage (openCubeSet U)
      (blockPairingIntegrand a W W))=integralAverage (openCubeSet Q) (blockPairingIntegrand a W W)
    simp_rw [←cubeAverage_eq_integralAverage_openCubeSet]
    exact (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q depth _
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
        (blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hmem hmem hEll))).symm
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
