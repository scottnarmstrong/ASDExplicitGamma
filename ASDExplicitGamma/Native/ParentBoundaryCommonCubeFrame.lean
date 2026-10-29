module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeGauge
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandCoefficient

/-! Exact physical true-frame identities on the common-square band. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- Exact physical coarse matrix in any positive observation frame. -/
theorem parent_boundary_common_cube_band_coarse_frame
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (σ : ℝ) (hσ : 0 < σ)
    {R : TriadicCube 2} {d : ℕ} (hR : R ∈ descendantsAtDepth P d) :
    coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu σ
        (parentBoundaryCommonOpenCubeCoefficient P (parentBoundaryCommonCubeBand P n height t ω))) =
      frameMatrix σ
        (coarseBlockMatrix (cubeSet R)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
  let f := parentBoundaryCommonCubeBand P n height t ω
  let k := parentBoundaryCellCoefficient hR f
  have hsource (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responseFramePlanarCoefficientField M.nu σ (parentBoundaryCommonOpenCubeCoefficient P f) x =
        responseFramePlanarCoefficientField M.nu σ k x := by
    change responsePlanarCoefficient (M.nu/σ)
        (responseCoefficientExtension (parentBoundaryCommonOpenCubeCoefficient P f) x/σ)=
      responsePlanarCoefficient (M.nu/σ) (responseCoefficientExtension k x/σ)
    rw [parent_boundary_common_open_cube_coefficient_value P f
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hx),
      parent_boundary_cell_coefficient_value hR f (openCubeSet_subset_cubeSet R hx)]
  have hframe : coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu σ (parentBoundaryCommonOpenCubeCoefficient P f)) =
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
    rw [parent_boundary_common_cube_band_apply M]
    exact native_source_planar_of_symm M.nu _ (native_source_band_attenuated_symm M n height t ω x)
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

/-- Every complete inverse history has the exact physical frame factor. -/
theorem parent_boundary_common_inverse_history_frame
    (Q : TriadicCube 2) (a af : CoeffField 2)
    {lam Lam laf Laf σ q : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEllFrame : IsEllipticFieldOn laf Laf (openCubeSet Q) af)
    (hσ : 0 < σ)
    (hMatrix : ∀ (R : TriadicCube 2) (d : ℕ)
      (_hR : R ∈ descendantsAtDepth Q d),
      coarseBlockMatrix (cubeSet R) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) a)) :
    lemmaVInverseHistory Q af q = σ * lemmaVInverseHistory Q a q := by
  have hdepth (d : ℕ) : lemmaVInverseDepthMax Q af d =
      σ * lemmaVInverseDepthMax Q a d := by
    rw [lemmaVInverseDepthMax,
      ← Scalar.inverse_history_framed_depth_max Q a hEll σ hσ d]
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    rw [Scalar.inverse_history_lowerRight R af
      (hEllFrame.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)), hMatrix R d hR]
    simp [frameMatrix]
  unfold lemmaVInverseHistory
  simp_rw [hdepth]
  calc
    (1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d *
        (σ * lemmaVInverseDepthMax Q a d) =
      (1 - q⁻¹) * (σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
        congr 1
        calc
          ∑' d : ℕ, (q⁻¹)^d * (σ * lemmaVInverseDepthMax Q a d) =
              ∑' d : ℕ, σ * ((q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
                apply tsum_congr
                intro d
                ring
          _ = σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d := tsum_mul_left
    _ = σ * ((1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by ring

/-- Restricting the same full physical band from a common parent gives
exactly the observation square's own full band coefficient. -/
theorem parent_boundary_common_cube_band_observed_eq
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    parentBoundaryCommonOpenCellCoefficient hQ (parentBoundaryCommonCubeBand P n height t ω) =
      parentBoundaryCommonOpenCubeCoefficient Q (parentBoundaryCommonCubeBand Q n height t ω) := by
  ext x
  change parentBoundaryCommonCubeBand P n height t ω _ =
    parentBoundaryCommonCubeBand Q n height t ω _
  rw [parent_boundary_common_cube_band_apply M,parent_boundary_common_cube_band_apply M]
  rfl

end
end ASDExplicitGamma.Native
