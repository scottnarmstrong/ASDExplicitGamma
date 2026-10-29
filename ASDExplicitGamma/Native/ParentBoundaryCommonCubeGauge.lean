module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeCarrier
public import ASDExplicitGamma.Native.ParentBoundaryHistoryCongr

/-! One common scalar center preserves every actual descendant inverse history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual open response coefficient on a translated source square. -/
def parentBoundaryCommonOpenCubeCoefficient (P : TriadicCube 2) :
    C(closure (cubeSet P),ℝ) →L[ℝ] ResponseCoefficient (openCubeSet P) :=
  parentBoundaryCommonOpenCellCoefficient (P := P) (Q := P) (d := 0) (by simp)

/-- Exact pointwise value on the actual open source square. -/
theorem parent_boundary_common_open_cube_coefficient_value
    (P : TriadicCube 2) (f : C(closure (cubeSet P),ℝ)) {x : Vec 2} (hx : x ∈ openCubeSet P) :
    responseCoefficientExtension (parentBoundaryCommonOpenCubeCoefficient P f) x =
      f ⟨x,subset_closure (openCubeSet_subset_cubeSet P hx)⟩ :=
  parent_boundary_common_open_cell_coefficient_value (P := P) (Q := P) (d := 0) (by simp) f hx

/-- Every descendant reciprocal block is unchanged by the same constant
scalar shear, with the frame held fixed. -/
theorem parent_boundary_common_descendant_inverse_block_gauge
    (P : TriadicCube 2) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet P),ℝ)) (g : ℝ)
    (W : TriadicCube 2) (d : ℕ) (hW : W∈descendantsAtDepth P d) :
    (coarseBlockMatrix (cubeSet W) (responseFramePlanarCoefficientField ν σ
      (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ g)))).lowerRight=
    (coarseBlockMatrix (cubeSet W) (responseFramePlanarCoefficientField ν σ
      (parentBoundaryCommonOpenCubeCoefficient P f))).lowerRight := by
  let k := σ⁻¹ • parentBoundaryCellCoefficient hW f
  have he (c : ℝ) : responseFramePlanarCoefficientField ν σ
      (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ c))=ᵐ[volume.restrict (openCubeSet W)]
      (fun x => responsePlanarCoefficient (ν/σ) (responseCoefficientExtension k x+c/σ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet W)] with x hx
    have hxopen := openCubeSet_subset_of_mem_descendantsAtDepth hW hx
    have hxW := openCubeSet_subset_cubeSet W hx
    rw [responseFramePlanarCoefficientField_apply,parent_boundary_common_open_cube_coefficient_value P _ hxopen,
      responseCoefficientExtension_smul_on _ _ hxW,parent_boundary_cell_coefficient_value hW f hxW]
    congr 1
    simp only [ContinuousMap.add_apply,ContinuousMap.const_apply]
    ring
  have hmat (c : ℝ) : coarseBlockMatrix (cubeSet W) (responseFramePlanarCoefficientField ν σ
      (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ c)))=
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
theorem parent_boundary_common_inverse_history_gauge
    (P : TriadicCube 2) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet P),ℝ)) (g : ℝ)
    (U : TriadicCube 2) (r : ℕ) (hU : U∈descendantsAtDepth P r) (a : ℝ) :
    lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ
      (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ g))) a=
    lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCubeCoefficient P f)) a := by
  let af := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCubeCoefficient P f)
  let ag := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ g))
  have hf := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet P) ν σ hν hσ
    (parentBoundaryCommonOpenCubeCoefficient P f)
  have hg := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet P) ν σ hν hσ
    (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ g))
  change lemmaVInverseHistory U ag a=lemmaVInverseHistory U af a
  apply parent_boundary_inverse_history_congr_blocks U ag af _ _ _ _
    (hg.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    (hf.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  intro d W hW
  have hWQ : W∈descendantsAtDepth P (r+d) := by
    simpa [Nat.add_comm] using mem_descendantsAtDepth_add hU hW
  exact parent_boundary_common_descendant_inverse_block_gauge P ν σ hν hσ f g W (r+d) hWQ

/-- Both source-tile maxima, with their respective complete-history
exponents, are invariant under one common scalar shear. -/
theorem parent_boundary_common_source_histories_gauge
    (P : TriadicCube 2) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet P),ℝ)) (g : ℝ) (mesh : ℕ) :
    let Q := P
    let a := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCubeCoefficient P f)
    let ag := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCubeCoefficient P (f+ContinuousMap.const _ g))
    lemmaVTileHistory Q mesh ag=lemmaVTileHistory Q mesh a ∧
      pureFluxSourceTileHistory Q mesh ag=pureFluxSourceTileHistory Q mesh a := by
  constructor
  · unfold lemmaVTileHistory
    apply Book.Ch02.finsetSupReal_congr
    intro U hU
    exact parent_boundary_common_inverse_history_gauge P ν σ hν hσ f g U mesh hU _
  · unfold pureFluxSourceTileHistory
    apply Book.Ch02.finsetSupReal_congr
    intro U hU
    exact parent_boundary_common_inverse_history_gauge P ν σ hν hσ f g U mesh hU _

/-- On every observed child, subtracting/restoring the SAME parent center
preserves both complete source-history maxima. The common center may lie
outside this child. -/
theorem parent_boundary_common_observed_histories_gauge
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet P),ℝ)) (g : ℝ) (mesh : ℕ) :
    let a := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCellCoefficient hQ f)
    let ag := responseFramePlanarCoefficientField ν σ
      (parentBoundaryCommonOpenCellCoefficient hQ (f+ContinuousMap.const _ g))
    lemmaVTileHistory Q mesh ag=lemmaVTileHistory Q mesh a ∧
      pureFluxSourceTileHistory Q mesh ag=pureFluxSourceTileHistory Q mesh a := by
  let R := ContinuousMap.compCLM ℝ ℝ (parentBoundaryCellClosedInclusion hQ)
  have he (c : ℝ) : parentBoundaryCommonOpenCellCoefficient hQ (f+ContinuousMap.const _ c) =
      parentBoundaryCommonOpenCubeCoefficient Q (R f+ContinuousMap.const _ c) := by
    ext x
    rfl
  have hf := he 0
  simp only [ContinuousMap.const_zero,add_zero] at hf
  dsimp only
  rw [he g,hf]
  exact parent_boundary_common_source_histories_gauge Q ν σ hν hσ (R f) g mesh

/-- Actual common-centered descendants inherit exactly the original physical
band inverse histories, including every depth and covariance correlation. -/
theorem parent_boundary_common_cube_actual_histories_gauge
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (mesh : ℕ) :
    let a := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonCubeObserved hQ n height t ω)
    let ag := responseFramePlanarCoefficientField ν σ (parentBoundaryCommonOpenCellCoefficient hQ
      (parentBoundaryCommonCubeBand P n height t ω))
    lemmaVTileHistory Q mesh ag=lemmaVTileHistory Q mesh a ∧
      pureFluxSourceTileHistory Q mesh ag=pureFluxSourceTileHistory Q mesh a := by
  have hh := parent_boundary_common_observed_histories_gauge hQ ν σ hν hσ
    (parentBoundaryCommonCubeCentered P n height t ω)
    (parentBoundaryCommonCubeCenterValue P n height t ω) mesh
  rw [←parent_boundary_common_cube_split] at hh
  exact hh

end
end ASDExplicitGamma.Native
