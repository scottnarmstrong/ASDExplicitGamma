module

public import ASDExplicitGamma.Main.HotCovPairedDrop
public import ASDExplicitGamma.Main.HotCovOrth
public import ASDExplicitGamma.Main.ETermMixedCarrier
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Scalar.CoefficientFlux
public import ASDExplicitGamma.Native.OldSignedDualReflection
public import ASDExplicitGamma.Native.OldSignedCellProjection

/-! MA-E-COVARIANCE, step 5: the affine receivers of the hot trial.  On a source
cell the receivers `-B_U^rec ν` (top loads) and `-T_U ν` (bottom loads) are, up
to the parent reciprocal field, the reciprocal block of the cell comparison
`W = S - L`.  The parent reciprocal fields are global gradients, which is what
the exact zero identity needs. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational

noncomputable section

/-- The cell restriction of the response coefficient. -/
def hotCovCellCoef (Q : TriadicCube 2) (d : ℕ)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) :
    ResponseCoefficient (openCubeSet U.val) :=
  oldSignedCellCoefficient Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k

/-- The affine receiver of a TOP load on the source cell `U`, for the cell-constant
datum `ν`: `-B_U^rec ν`. -/
def hotCovTopRcv (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d)
    (ν : Vec 2) : Vec 2 → Vec 2 :=
  mainECellTopAffineReceiver U.val
    (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
      nu sigma hnu hsigma (hotCovCellCoef Q d k U)) ν

/-- The affine receiver of a BOTTOM load on the source cell `U`: `-T_U ν`. -/
def hotCovBotRcv (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d)
    (ν : Vec 2) : Vec 2 → Vec 2 :=
  mainECellBottomAffineReceiver U.val
    (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
      nu sigma hnu hsigma (hotCovCellCoef Q d k U)) ν

/-- The reciprocal block of the parent canonical minimizer for the load `P`. -/
def hotCovParentRecip (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (x : Vec 2) : Vec 2 :=
  (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x)).2

private theorem hotCov_blockMatVecMul_sub {d : ℕ} (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have h := blockMatVecMul_add A (X - Y) Y
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-- The cell comparison's reciprocal block is, almost everywhere on the cell, the
sum of the (negated) cell flux and the parent flux: the parent flux minus the
cell flux. -/
theorem hotCov_cell_flux_split (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (P : BlockVec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      (scalarCoefficientFlux
        (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
        (oldSignedCanonicalAffineField U.val
          (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
          (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
            nu sigma hnu hsigma (hotCovCellCoef Q d k U)) P) x).2 =
      hotCovParentRecip Q nu sigma hnu hsigma k P x -
        hotCovCmpRecip Q d nu sigma hnu hsigma k U P x := by
  filter_upwards [old_signed_cell_frame_coefficient_ae Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma k] with x hx
  have hL : (oldSignedCanonicalAffineField U.val
      (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
        nu sigma hnu hsigma (hotCovCellCoef Q d k U)) P : Vec 2 → BlockVec 2) x =
      (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma
        (hotCovCellCoef Q d k U) P : Vec 2 → BlockVec 2) x := rfl
  simp only [scalarCoefficientFlux, hotCovParentRecip, hotCovCmpRecip, hotCovCmp,
    oldHessianParentCellComparison]
  change (blockMatVecMul (blockCoeffField _ x) _).2 = _
  rw [hL]
  have hc : blockCoeffField
      (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) x =
      blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x := by
    have hx' : responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U) x =
        responseFramePlanarCoefficientField nu sigma k x := hx
    simp only [blockCoeffField, hx']
  rw [hc]
  have hsub : (((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x).1 -
      ((oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
        Vec 2 → BlockVec 2) x).1,
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x).2 -
      ((oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
        Vec 2 → BlockVec 2) x).2) =
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x -
      (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
        Vec 2 → BlockVec 2) x := rfl
  have hev : ∀ (A : BlockMat 2), (blockMatVecMul A
      (({ potential := fun x =>
            ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x).1 -
              ((oldSignedFrameCanonicalField U.val nu sigma hnu hsigma
                (oldSignedCellCoefficient Q U.val
                  (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) P :
                Vec 2 → BlockVec 2) x).1,
          flux := fun x =>
            ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x).2 -
              ((oldSignedFrameCanonicalField U.val nu sigma hnu hsigma
                (oldSignedCellCoefficient Q U.val
                  (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) P :
                Vec 2 → BlockVec 2) x).2 } : BlockState 2).eval x)) =
      blockMatVecMul A
        ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x -
          (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
            Vec 2 → BlockVec 2) x) := fun A => rfl
  rw [hev, hotCov_blockMatVecMul_sub]
  simp

/-- Top-load receiver: the reciprocal block of the cell comparison for the bottom
load `(0,ν)`, minus the parent reciprocal field shifted by `ν`. -/
theorem hotCov_topRcv_split (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      hotCovTopRcv Q d nu sigma hnu hsigma k U ν x =
        hotCovCmpRecip Q d nu sigma hnu hsigma k U (0, ν) x -
          (hotCovParentRecip Q nu sigma hnu hsigma k (0, ν) x - ν) := by
  filter_upwards [hotCov_cell_flux_split Q d nu sigma hnu hsigma k U (0, ν)] with x hx
  change -((scalarCoefficientFlux _ _ x).2 - ν) = _
  rw [hx]
  abel

/-- Bottom-load receiver: the reciprocal block of the cell comparison for the top
load `(ν,0)`, minus the parent reciprocal field. -/
theorem hotCov_botRcv_split (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      hotCovBotRcv Q d nu sigma hnu hsigma k U ν x =
        hotCovCmpRecip Q d nu sigma hnu hsigma k U (ν, 0) x -
          hotCovParentRecip Q nu sigma hnu hsigma k (ν, 0) x := by
  filter_upwards [hotCov_cell_flux_split Q d nu sigma hnu hsigma k U (ν, 0)] with x hx
  change -((scalarCoefficientFlux _ _ x).2) = _
  rw [hx]
  abel

local instance hotCovReceiverFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The parent reciprocal field is a global gradient. -/
theorem hotCov_parent_recip_potential (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    IsPotentialOn (openCubeSet Q) (hotCovParentRecip Q nu sigma hnu hsigma k P) :=
  (old_signed_reflected_canonical_compatible Q nu sigma hnu hsigma k P).2.1

/-- The exact zero identity for the parent reciprocal field: `J ∇(Iw)` is orthogonal
to every gradient of an `H¹` function, and to every constant, in the whole parent
cube. -/
theorem hotCov_parent_orth (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (ν : Vec 2)
    (w : H10Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q, vecDot
      (planarQuarterTurn ((diagInterpolant Q d w.toH1Function).grad x))
      (hotCovParentRecip Q nu sigma hnu hsigma k P x - ν) ∂volume = 0 := by
  obtain ⟨g, hg⟩ := hotCov_parent_recip_potential Q nu sigma hnu hsigma k P
  let aff := H1Function.affineOnIsSobolevRegularDomain
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain ν
  have hgrad : (g - aff).grad = fun x => hotCovParentRecip Q nu sigma hnu hsigma k P x - ν := by
    rw [H1Function.sub_grad]
    funext x
    rw [hg]
    simp [aff]
  have h := hotcov_rot_grad_orth_of_memH10 (isOpenBoundedConvexDomain_openCubeSet Q).isOpen
    (diagInterpolant Q d w.toH1Function) (g - aff) (diagInterpolant_h10_memH10 Q d w)
  rw [hgrad] at h
  exact h

end

end ASDExplicitGamma.Main
