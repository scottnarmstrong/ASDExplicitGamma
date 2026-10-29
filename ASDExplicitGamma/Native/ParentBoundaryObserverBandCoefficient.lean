module

public import ASDExplicitGamma.Native.ParentBoundaryObserverBandHeat
public import ASDExplicitGamma.Native.GenericSourceBandCoefficient
public import ASDExplicitGamma.Native.ParentBoundaryBandCellMoments

/-! Exact physical and normalized observer-square coefficients for the same finite band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The actual observer scalar is the physical band entry at every closed-cube point. -/
theorem parent_boundary_observer_band_scalar_apply (M : ABKModel 2) (q n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : closure (cubeSet (originCube 2 q))) :
    parentBoundaryObserverBandScalar q n height t ω x =
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω x 1 0 := by
  let K := closure (cubeSet (originCube 2 q))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  simp only [parentBoundaryObserverBandScalar,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    modelBand,ContinuousMap.sum_apply,smul_eq_mul]
  rw [olderField_apply_eq_coefficientCutoff K M ell n hK ω x]
  rw [Finset.mul_sum]
  have hsum := native_source_band_index_sum n height
    (fun j => Real.sqrt t*(shellFieldScalarRestriction K (ω.1 j) x))
  rw [hsum]
  simp only [attenuatedCoefficient,Matrix.add_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  rfl

theorem parent_boundary_observer_band_coefficient_on_cube (M : ABKModel 2) (q n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) (hx : x ∈ cubeSet (originCube 2 q)) :
    responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ
        (parentBoundaryObserverBandScalar q n height t ω)) x =
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω x := by
  rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hx,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,parent_boundary_observer_band_scalar_apply]
  exact native_source_planar_of_symm M.nu _ (native_source_band_attenuated_symm M n height t ω x)

theorem parent_boundary_observer_band_coarse_matrix_frame
    (M : ABKModel 2) (q n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    {R : TriadicCube 2} {d : ℕ} (hR : R ∈ descendantsAtDepth (originCube 2 q) d) :
    coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction q (parentBoundaryObserverBandScalar q n height t ω))) =
      frameMatrix (Annealed.sigmaBar M n:ℝ)
        (coarseBlockMatrix (cubeSet R)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
  let P := originCube 2 n
  let f := parentBoundaryObserverBandScalar q n height t ω
  let k := parentBoundaryCellCoefficient hR f
  let σ : ℝ := Annealed.sigmaBar M n
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hsource (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction q f) x =
        responseFramePlanarCoefficientField M.nu σ k x := by
    change responsePlanarCoefficient (M.nu/σ)
        (responseCoefficientExtension (pureFluxOpenResponseRestriction q f) x/σ)=
      responsePlanarCoefficient (M.nu/σ) (responseCoefficientExtension k x/σ)
    rw [pureFluxOpenResponseRestriction_value q f
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hx),
      parent_boundary_cell_coefficient_value hR f (openCubeSet_subset_cubeSet R hx)]
  have hframe : coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction q f)) =
      coarseBlockMatrix (cubeSet R) (responseFramePlanarCoefficientField M.nu σ k) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hsource x hx
  have hphysical (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responsePlanarCoefficientField M.nu k x =
        attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω x := by
    change responsePlanarCoefficient M.nu (responseCoefficientExtension k x)=_
    rw [parent_boundary_cell_coefficient_value hR f (openCubeSet_subset_cubeSet R hx)]
    have hxP := (cubeSet_subset_of_mem_descendantsAtDepth hR) (openCubeSet_subset_cubeSet R hx)
    have hh := parent_boundary_observer_band_coefficient_on_cube M q n height t ω x hxP
    rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hxP,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply] at hh
    exact hh
  have hphysicalMatrix : coarseBlockMatrix (cubeSet R) (responsePlanarCoefficientField M.nu k) =
      coarseBlockMatrix (cubeSet R)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hphysical x hx
  calc
    _ = coarseBlockMatrix (cubeSet R) (responseFramePlanarCoefficientField M.nu σ k) := hframe
    _ = frameMatrix σ (coarseBlockMatrix (cubeSet R) (responsePlanarCoefficientField M.nu k)) :=
      response_coarseMatrix_frame_eq (measurableSet_cubeSet R) M.nu σ M.nu_pos hσ k
    _ = _ := by rw [hphysicalMatrix]

end
end ASDExplicitGamma.Native
