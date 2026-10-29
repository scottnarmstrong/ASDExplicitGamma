module

public import ASDExplicitGamma.Native.ParentBoundaryShearTrace
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandBank
public import ASDExplicitGamma.Gaussian.GaussCentering
public import ASDExplicitGamma.Native.ParentBoundaryBandCellMoments
public import ASDExplicitGamma.Native.ParentBoundaryHistoryCongr

/-! Constant physical centers preserve every complete descendant inverse history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- Every descendant reciprocal block is unchanged by the same constant
scalar shear, with the frame held fixed. -/
theorem parent_boundary_descendant_inverse_block_gauge
    (q : ℤ) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet (originCube 2 q)),ℝ)) (g : ℝ)
    (W : TriadicCube 2) (d : ℕ) (hW : W∈descendantsAtDepth (originCube 2 q) d) :
    (coarseBlockMatrix (cubeSet W) (responseFramePlanarCoefficientField ν σ
      (pureFluxOpenResponseRestriction q (f+ContinuousMap.const _ g)))).lowerRight=
    (coarseBlockMatrix (cubeSet W) (responseFramePlanarCoefficientField ν σ
      (pureFluxOpenResponseRestriction q f))).lowerRight := by
  let k := σ⁻¹ • parentBoundaryCellCoefficient hW f
  have he (c : ℝ) : responseFramePlanarCoefficientField ν σ
      (pureFluxOpenResponseRestriction q (f+ContinuousMap.const _ c))=ᵐ[volume.restrict (openCubeSet W)]
      (fun x => responsePlanarCoefficient (ν/σ) (responseCoefficientExtension k x+c/σ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet W)] with x hx
    have hxopen := openCubeSet_subset_of_mem_descendantsAtDepth hW hx
    have hxW := openCubeSet_subset_cubeSet W hx
    rw [responseFramePlanarCoefficientField_apply,pureFluxOpenResponseRestriction_value q _ hxopen,
      responseCoefficientExtension_smul_on _ _ hxW,parent_boundary_cell_coefficient_value hW f hxW]
    congr 1
    simp only [ContinuousMap.add_apply,ContinuousMap.const_apply]
    ring
  have hmat (c : ℝ) : coarseBlockMatrix (cubeSet W) (responseFramePlanarCoefficientField ν σ
      (pureFluxOpenResponseRestriction q (f+ContinuousMap.const _ c)))=
      coarseBlockMatrix (cubeSet W) (fun x => responsePlanarCoefficient (ν/σ) (responseCoefficientExtension k x+c/σ)) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube W,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube W]
    exact coarseBlockMatrix_congr_of_ae_eq (he c)
  rw [hmat g]
  have hm0 := hmat 0
  simp only [ContinuousMap.const_zero,add_zero,zero_div,add_zero] at hm0
  rw [hm0]
  exact coarse_lowerRight_constantSkew (ν/σ) (div_pos hν hσ) k (g/σ)

/-- Constant centers preserve the ENTIRE inverse history on every source
cell, not merely one finite term of its Haar series. -/
theorem parent_boundary_inverse_history_gauge
    (q : ℤ) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet (originCube 2 q)),ℝ)) (g : ℝ)
    (U : TriadicCube 2) (r : ℕ) (hU : U∈descendantsAtDepth (originCube 2 q) r) (a : ℝ) :
    lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ
      (pureFluxOpenResponseRestriction q (f+ContinuousMap.const _ g))) a=
    lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction q f)) a := by
  let af := responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction q f)
  let ag := responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction q (f+ContinuousMap.const _ g))
  have hf := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 q)) ν σ hν hσ
    (pureFluxOpenResponseRestriction q f)
  have hg := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 q)) ν σ hν hσ
    (pureFluxOpenResponseRestriction q (f+ContinuousMap.const _ g))
  change lemmaVInverseHistory U ag a=lemmaVInverseHistory U af a
  apply parent_boundary_inverse_history_congr_blocks U ag af _ _ _ _
    (hg.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    (hf.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  intro d W hW
  have hWQ : W∈descendantsAtDepth (originCube 2 q) (r+d) := by
    simpa [Nat.add_comm] using mem_descendantsAtDepth_add hU hW
  exact parent_boundary_descendant_inverse_block_gauge q ν σ hν hσ f g W (r+d) hWQ

end
end ASDExplicitGamma.Native
