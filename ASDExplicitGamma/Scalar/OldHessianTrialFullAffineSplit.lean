module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenSpatialContraction
public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredAffineSpatial
public import ASDExplicitGamma.Scalar.OldHessianTrialFullModeColumns

/-! Literal full affine source split, retaining its positive source sign. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- One actual positive full-source/affine-TOP cross, before freezing. -/
def oldHessianFullAffineSpatialMode (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (j : whiteBasisIndex) : ℝ :=
  oldSignedCellAverage Q (coarse+1) (fun U => ∑ i : Fin 2,cubeAverage U.val (fun x =>
    vecDot (oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L (j,i) U x)
      (-oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L (j,i) x)))

/-- Exact integrated cell decomposition into frozen and centered sources.
The source sign and all product integrability are proved, not postulated. -/
theorem old_hessian_full_affine_cell_split (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q (coarse+1)) :
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k p.2
    let R := oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L p U
    cubeAverage U.val (fun x => vecDot (R x) (-oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p x))=
      cubeAverage U.val (fun x => vecDot
        ((cubeAverage U.val (q3Convolution b L h3Zero (whiteBasis p.1))) •
          matVecMul responsePlanarJ ((diagInterpolant Q (coarse+1) u.toH1Function).grad x)) (R x))+
      cubeAverage U.val (fun x => vecDot (R x)
        (oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U.val x)) := by
  intro u R
  let F := fun x => -oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p x
  let C := oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U.val
  let W := fun x => (cubeAverage U.val (q3Convolution b L h3Zero (whiteBasis p.1))) •
    matVecMul responsePlanarJ ((diagInterpolant Q (coarse+1) u.toH1Function).grad x)
  have he : W=(fun x => F x-C x) := by
    funext x
    change _= -oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p x-
      (-oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p x-W x)
    abel
  have hFm (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure U.val) := by
    have hm := (old_hessian_mixed_bottom_source_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2).mono_measure
      (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth U.property))
    exact (memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hm) i)).neg
  have hCm (i : Fin 2) := (old_hessian_centered_mode_regular Q coarse nu sigma hnu hsigma k b L p U.val U.property i).1
  have hRm (i : Fin 2) := old_hessian_minus_affine_spatial_column_memLp Q (coarse+1) nu sigma hnu hsigma k b L p U i
  have hh := old_hessian_vector_pairing_sub U.val F C R hFm hCm hRm
  have hepoint (x) : W x=F x-C x := congrFun he x
  simp_rw [←hepoint] at hh
  have hRF : cubeAverage U.val (fun x => vecDot (R x) (F x))=cubeAverage U.val (fun x => vecDot (F x) (R x)) :=
    congrArg (cubeAverage U.val) (funext fun x => vecDot_comm (R x) (F x))
  have hRC : cubeAverage U.val (fun x => vecDot (R x) (C x))=cubeAverage U.val (fun x => vecDot (C x) (R x)) :=
    congrArg (cubeAverage U.val) (funext fun x => vecDot_comm (R x) (C x))
  change cubeAverage U.val (fun x => vecDot (R x) (F x))=
    cubeAverage U.val (fun x => vecDot (W x) (R x))+cubeAverage U.val (fun x => vecDot (R x) (C x))
  rw [hRF,hRC]
  linarith only [hh]

/-- The literal full two-load mode splits into its exact frozen signed
mode and the same centered modes paid in the fourth OLD bill. -/
theorem old_hessian_full_affine_mode_split (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (lam : ℝ) (j : whiteBasisIndex) :
    2*lam*oldHessianFullAffineSpatialMode Q coarse nu sigma hnu hsigma k b L j=
      oldHessianFrozenSpatialTerm Q coarse nu sigma hnu hsigma k b L lam j+
        2*lam*(∑ i : Fin 2,oldHessianCenteredAffineSpatialTerm Q coarse nu sigma hnu hsigma k b L (j,i)) := by
  unfold oldHessianFullAffineSpatialMode
  simp_rw [old_hessian_full_affine_cell_split]
  simp only [Finset.sum_add_distrib,old_signed_cell_average_add]
  unfold oldHessianFrozenSpatialTerm oldHessianCenteredAffineSpatialTerm
  simp only [old_signed_cell_average_mul,old_signed_cell_average_sum]
  dsimp only [oldHessianMinusAffineSpatialColumn,oldHessianMinusMeanColumn]
  ring

end
end ASDExplicitGamma.Scalar
