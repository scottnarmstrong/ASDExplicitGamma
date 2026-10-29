module

public import ASDExplicitGamma.Scalar.OldHessianTrialAffineReceiverColumns
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusOscillation
public import ASDExplicitGamma.Native.OldSignedAffineResidualSplit
public import ASDExplicitGamma.Native.OldSignedAffineIdentification

/-! Exact affine/oscillatory reciprocal split of the unchanged original minus. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The genuine original fine minus flux is its local TOP reciprocal
column plus its own centered reciprocal residual, in the same medium. -/
theorem old_hessian_minus_flux_split (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) :
    let kU := oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k
    let Z := oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L p.1 p.2) (old_signed_flat_minus_block_memL2 Q b L p.1 p.2)
    (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma kU) Z x).2)=ᵐ[
      volumeMeasureOn (openCubeSet U.val)]
    (fun x => oldHessianMinusAffineSpatialColumn Q fine nu sigma hnu hsigma k b L p U x+
      oldHessianMinusOscillationColumn Q fine nu sigma hnu hsigma k b L p U x) := by
  intro kU Z
  let F := oldSignedFlatMinusBlock Q b L p.1 p.2
  let q := oldHessianMinusMeanColumn Q fine b L p U
  have hm : oldSignedBlockMean U.val F=(q,0) := by
    simp only [q,oldHessianMinusMeanColumn,oldSignedFlatInput,Bool.false_eq_true,ite_false]
    simp [F,oldSignedFlatMinusBlock,oldSignedBlockMean,cubeAverage_const]
    rfl
  have hF : MemBlockL2 (openCubeSet U.val) F :=
    old_signed_flat_input_cell_memL2 Q fine b L false p.1 p.2 U.val U.property
  let HG1 := toHilbertBlockL2OfBlockField (hF.sub (memLp_const (q,0)))
  let HG2 := toHilbertBlockL2OfBlockField (hF.sub (memLp_const (oldSignedBlockMean U.val F)))
  have hclasses : HG1=HG2 := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField (hF.sub (memLp_const (q,0))),
      coeFn_toHilbertBlockL2OfBlockField (hF.sub (memLp_const (oldSignedBlockMean U.val F)))] with x hx hy
    exact hx.trans ((congrArg HilbertBlockVec.ofBlockVec (by rw [hm])).trans hy.symm)
  have hh := old_signed_residual_mean_split_ae U.val nu sigma hnu hsigma kU F
    (old_signed_flat_input_cell_memL2 Q fine b L false p.1 p.2 U.val U.property)
  dsimp only at hh
  rw [hm,old_signed_affine_residual_field] at hh
  filter_upwards [hh] with x hx
  change (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (Z x)).2=_
  change Z x=_ at hx
  rw [hx]
  change (blockMatVecMul _ (_+_)).2=(blockMatVecMul _ _).2+(blockMatVecMul _ _).2
  rw [blockMatVecMul_add]
  simp only [Prod.snd_add]
  apply congrArg₂ (·+·)
  · rfl
  · change (blockMatVecMul _ (scalarResidualField U.val nu sigma hnu hsigma kU HG1 x)).2=
      (blockMatVecMul _ (scalarResidualField U.val nu sigma hnu hsigma kU HG2 x)).2
    rw [hclasses]

end
end ASDExplicitGamma.Scalar
