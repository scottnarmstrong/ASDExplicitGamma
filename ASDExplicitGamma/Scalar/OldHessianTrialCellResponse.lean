module

public import ASDExplicitGamma.Scalar.OldHessianTrialPairedWeak
public import ASDExplicitGamma.Native.OldSignedCanonicalResponseSpace
public import ASDExplicitGamma.Native.OldSignedCellHistories

/-! The actual parent-minus-coarse-cell comparison is a homogeneous response
on that cell, without assigning affine boundary data to the parent restriction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- Response-space equations depend on the physical coefficient only a.e. -/
theorem old_hessian_response_coefficient_congr {U : Set (Vec 2)}
    {a b : CoeffField 2} {W : BlockState 2}
    (hab : a =ᵐ[volumeMeasureOn U] b) (hW : BlockResponseSpace a U W) :
    BlockResponseSpace b U W := by
  refine ⟨hW.1,hW.2.1,?_⟩
  intro Y hY
  have he : (fun x => blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField b x) (W.eval x))) =ᵐ[
      volumeMeasureOn U]
      (fun x => blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (W.eval x))) := by
    filter_upwards [hab] with x hx
    change blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixOfCoeff (b x)) (W.eval x)) =
      blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixOfCoeff (a x)) (W.eval x))
    rw [hx]
  rw [integral_congr_ae he]
  exact hW.2.2 Y hY

/-- The exact difference of the physical parent and coarse cell minimizers. -/
def oldHessianParentCellComparison (Q D : TriadicCube 2)
    (hD : openCubeSet D ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) : BlockState 2 :=
  let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  let L := oldSignedFrameCanonicalField D nu sigma hnu hsigma (oldSignedCellCoefficient Q D hD k) P
  ⟨fun x => (S x).1-(L x).1,fun x => (S x).2-(L x).2⟩

theorem old_hessian_parent_cell_comparison_memL2 (Q D : TriadicCube 2)
    (hD : openCubeSet D ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet D)
      (oldHessianParentCellComparison Q D hD nu sigma hnu hsigma k P).eval :=
  ((Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)).mono_measure
    (Measure.restrict_mono_set volume hD)).sub
      (Lp.memLp (oldSignedFrameCanonicalField D nu sigma hnu hsigma (oldSignedCellCoefficient Q D hD k) P))

/-- Both fields solve the same local homogeneous equations after restriction
and coefficient identification. Their difference therefore does too. -/
theorem old_hessian_parent_cell_comparison_response (Q D : TriadicCube 2)
    (hD : openCubeSet D ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    BlockResponseSpace (responseFramePlanarCoefficientField nu sigma k) (openCubeSet D)
      (oldHessianParentCellComparison Q D hD nu sigma hnu hsigma k P) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let kD := oldSignedCellCoefficient Q D hD k
  let X := oldSignedCanonicalBlockState Q nu sigma hnu hsigma k P
  let Y := oldSignedCanonicalBlockState D nu sigma hnu hsigma kD P
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hXmem : MemBlockL2 (openCubeSet Q) X.eval := Lp.memLp _
  have hYmem : MemBlockL2 (openCubeSet D) Y.eval := Lp.memLp _
  have hX := blockResponseSpace_restrict_subcube Q D hD a hEll X
    (old_signed_canonical_response_space Q nu sigma hnu hsigma k P) hXmem
  have hY := old_hessian_response_coefficient_congr
    (old_signed_cell_frame_coefficient_ae Q D hD nu sigma k)
    (old_signed_canonical_response_space D nu sigma hnu hsigma kD P)
  have hh := blockResponseSpace_sub
    (hEll.mono (measurableSet_openCubeSet D) hD) X Y hX hY
    (hXmem.mono_measure (Measure.restrict_mono_set volume hD)) hYmem
  have he : oldHessianParentCellComparison Q D hD nu sigma hnu hsigma k P=X+(-1:ℝ) • Y := by
    apply BlockState.ext
    · funext x
      change _-_ = _+(-1:ℝ) • (oldSignedFrameCanonicalField D nu sigma hnu hsigma kD P x).1
      simp only [neg_one_smul,sub_eq_add_neg]
      rfl
    · funext x
      change _-_ = _+(-1:ℝ) • (oldSignedFrameCanonicalField D nu sigma hnu hsigma kD P x).2
      simp only [neg_one_smul,sub_eq_add_neg]
      rfl
  rw [he]
  exact hh

end
end ASDExplicitGamma.Scalar
