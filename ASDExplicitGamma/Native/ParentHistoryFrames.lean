module

public import ASDExplicitGamma.Native.ParentBoundaryBandMaxTraceMoment
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryTheta

/-! Actual physical and common-centered frames for complete history restoration.
The frame identities are adapted from an earlier version of the argument. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal Nat
noncomputable section

theorem parent_history_finset_sup_ofReal {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    ENNReal.ofReal (Book.Ch02.finsetSupReal s f) =
      s.sup (fun i => ENNReal.ofReal (f i)) := by
  have hh := bank_finite_max_ofReal s hs f
  have huniv : (Finset.univ : Finset ↥s) = s.attach := by
    ext i
    simp
  calc
    _ = (Finset.univ : Finset ↥s).sup (fun i => ENNReal.ofReal (f i.1)) := by
      simpa only [historyFiniteMax] using hh.symm
    _ = s.attach.sup (fun i => ENNReal.ofReal (f i.1)) := by rw [huniv]
    _ = s.sup (fun i => ENNReal.ofReal (f i)) :=
      Finset.sup_attach s (fun i => ENNReal.ofReal (f i))

def parentHistoryPhysicalFrame (M : ABKModel 2) (P : TriadicCube 2)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (parentBoundaryCommonOpenCubeCoefficient P
      (parentBoundaryCommonCubeBand P n height t ω))

def parentHistoryCenteredFrame (M : ABKModel 2) (P : TriadicCube 2)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
  responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (parentBoundaryCommonOpenCubeCoefficient P
      (parentBoundaryCommonCubeCentered P n height t ω))

theorem parent_history_frame_cell_matrix
    (M : ABKModel 2) {P R : TriadicCube 2} {j : ℕ}
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (centered : Bool) :
    coarseBlockMatrix (openCubeSet R)
        (if centered then parentHistoryCenteredFrame M P n height t ω
          else parentHistoryPhysicalFrame M P n height t ω) =
      frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu
            (if centered then parentBoundaryCellCoefficient hR
                (parentBoundaryCommonCubeCentered P n height t ω)
              else parentBoundaryCellCoefficient hR
                (parentBoundaryCommonCubeBand P n height t ω)))) := by
  have hσ : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hrestr (f : C(closure (cubeSet P), ℝ)) :
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonOpenCubeCoefficient P f) =ᵐ[volume.restrict (openCubeSet R)]
      responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCellCoefficient hR f) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    rw [responseFramePlanarCoefficientField_apply,
      responseFramePlanarCoefficientField_apply,
      parent_boundary_common_open_cube_coefficient_value P f
        (openCubeSet_subset_of_mem_descendantsAtDepth hR hx),
      parent_boundary_cell_coefficient_value hR f
        (openCubeSet_subset_cubeSet R hx)]
  cases centered with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      change coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (parentBoundaryCommonOpenCubeCoefficient P
              (parentBoundaryCommonCubeBand P n height t ω))) = _
      rw [coarseBlockMatrix_congr_of_ae_eq (hrestr _)]
      rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeBand P n height t ω)))]
      exact response_coarseMatrix_frame_eq (measurableSet_cubeSet R) M.nu
        (Annealed.sigmaBar M n) M.nu_pos hσ
        (parentBoundaryCellCoefficient hR
          (parentBoundaryCommonCubeBand P n height t ω))
  | true =>
      simp only [ite_true]
      change coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (parentBoundaryCommonOpenCubeCoefficient P
              (parentBoundaryCommonCubeCentered P n height t ω))) = _
      rw [coarseBlockMatrix_congr_of_ae_eq (hrestr _)]
      rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeCentered P n height t ω)))]
      exact response_coarseMatrix_frame_eq (measurableSet_cubeSet R) M.nu
        (Annealed.sigmaBar M n) M.nu_pos hσ
        (parentBoundaryCellCoefficient hR
          (parentBoundaryCommonCubeCentered P n height t ω))

theorem parent_history_physical_depth
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    parentBoundaryBandTraceDepthMax M n height P t j ω =
      ENNReal.ofReal (oldSignedMaxTraceDepth P (parentHistoryPhysicalFrame M P n height t ω) j) := by
  classical
  have hs : (descendantsAtDepth P j).Nonempty := descendantsAtDepth_nonempty P j
  have htrace (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth P j) :
      traceDefect (cubeSet R)
          (attenuatedCoefficient M n (n + (height : ℤ)) (fun _ => Real.sqrt t) ω)
          (Annealed.sigmaBar M n) =
        traceDefect (openCubeSet R) (parentHistoryPhysicalFrame M P n height t ω) 1 := by
    have hm := parent_boundary_common_cube_band_coarse_frame M P n height t ω
      (Annealed.sigmaBar M n) (Annealed.sigmaBar_characterization M n).1 hR
    have hm' : coarseBlockMatrix (openCubeSet R)
        (parentHistoryPhysicalFrame M P n height t ω) =
        frameMatrix (Annealed.sigmaBar M n)
          (coarseBlockMatrix (cubeSet R)
            (attenuatedCoefficient M n (n + (height : ℤ)) (fun _ => Real.sqrt t) ω)) := by
      calc
        _ = coarseBlockMatrix (cubeSet R) (parentHistoryPhysicalFrame M P n height t ω) :=
          (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
            (parentHistoryPhysicalFrame M P n height t ω)).symm
        _ = _ := hm
    unfold traceDefect
    rw [hm']
    simp [frameMatrix, Matrix.trace_smul, smul_eq_mul]
  unfold parentBoundaryBandTraceDepthMax oldSignedMaxTraceDepth
  change (descendantsAtDepth P j).sup (fun R => ENNReal.ofReal
      (traceDefect (cubeSet R)
        (attenuatedCoefficient M n (n + (height : ℤ)) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M n))) = _
  have hsup : (descendantsAtDepth P j).sup (fun R => ENNReal.ofReal
      (traceDefect (cubeSet R)
        (attenuatedCoefficient M n (n + (height : ℤ)) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M n))) =
      (descendantsAtDepth P j).sup (fun R => ENNReal.ofReal
        (traceDefect (openCubeSet R) (parentHistoryPhysicalFrame M P n height t ω) 1)) := by
    apply Finset.sup_congr rfl
    intro R hR
    rw [htrace R hR]
  rw [parent_history_finset_sup_ofReal (descendantsAtDepth P j) hs
    (fun R => traceDefect (openCubeSet R)
      (parentHistoryPhysicalFrame M P n height t ω) 1)]
  exact hsup

theorem parent_history_centered_cell_trace
    (M : ABKModel 2) {P R : TriadicCube 2} {j : ℕ}
    (hR : R ∈ descendantsAtDepth P j) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    squareTrace R M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonCubeObserved hR n height t ω) =
      traceDefect (openCubeSet R)
        (parentHistoryCenteredFrame M P n height t ω) 1 := by
  have hcell := parent_boundary_common_cell_trace_eq hR M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (parentBoundaryCommonCubeCentered P n height t ω)
  have hm := parent_history_frame_cell_matrix M hR n height t ω true
  have hm' : coarseBlockMatrix (openCubeSet R)
        (parentHistoryCenteredFrame M P n height t ω) =
      frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu
            (parentBoundaryCellCoefficient hR
              (parentBoundaryCommonCubeCentered P n height t ω)))) := by
    exact hm
  have hnorm : traceDefect (openCubeSet R)
      (parentHistoryCenteredFrame M P n height t ω) 1 =
      traceDefect (cubeSet R)
        (responsePlanarCoefficientField M.nu
          (parentBoundaryCellCoefficient hR
            (parentBoundaryCommonCubeCentered P n height t ω)))
        (Annealed.sigmaBar M n) := by
    unfold traceDefect
    rw [hm']
    simp [frameMatrix, Matrix.trace_smul, smul_eq_mul]
  simpa only [parentBoundaryCommonCubeObserved] using hcell.trans hnorm.symm

theorem parent_history_centered_depth
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    parentBoundaryCommonCenteredDepthMax M P n height t j ω =
      ENNReal.ofReal (oldSignedMaxTraceDepth P (parentHistoryCenteredFrame M P n height t ω) j) := by
  classical
  let S := descendantsAtDepth P j
  let f := fun R : TriadicCube 2 =>
    traceDefect (openCubeSet R) (parentHistoryCenteredFrame M P n height t ω) 1
  have htrace (R : ↥S) :
      squareTrace R.1 M.nu (Annealed.sigmaBar M n)
          (parentBoundaryCommonCubeObserved R.2 n height t ω) = f R.1 := by
    exact parent_history_centered_cell_trace M R.2 n height t ω
  have huniv : (Finset.univ : Finset ↥S) = S.attach := by
    ext R
    simp [S]
  unfold parentBoundaryCommonCenteredDepthMax oldSignedMaxTraceDepth
  change (Finset.univ : Finset ↥S).sup (fun R => ENNReal.ofReal
      (squareTrace R.1 M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonCubeObserved R.2 n height t ω))) =
      ENNReal.ofReal (Book.Ch02.finsetSupReal S f)
  calc
    _ = (Finset.univ : Finset ↥S).sup (fun R => ENNReal.ofReal (f R.1)) := by
      apply Finset.sup_congr rfl
      intro R _
      rw [htrace R]
    _ = S.sup (fun R => ENNReal.ofReal (f R)) := by
      rw [huniv]
      exact Finset.sup_attach S (fun R => ENNReal.ofReal (f R))
    _ = ENNReal.ofReal (Book.Ch02.finsetSupReal S f) :=
      (parent_history_finset_sup_ofReal S (by simpa [S] using descendantsAtDepth_nonempty P j) f).symm

theorem parent_history_physical_history
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    parentBoundaryBandMaxTraceHistory M n height P t ω =
      ENNReal.ofReal (oldSignedMaxTraceHistory P
        (parentHistoryPhysicalFrame M P n height t ω)) := by
  let a := parentHistoryPhysicalFrame M P n height t ω
  let σ : ℝ := Annealed.sigmaBar M n
  have hEll : IsEllipticFieldOn (M.nu / σ)
      (((M.nu / σ)^2 + (‖parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeBand P n height t ω)‖ / σ)^2) / (M.nu / σ))
      (openCubeSet P) a := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1
      (parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeBand P n height t ω))
  have hs := old_signed_max_trace_series_summable P a hEll
  have hn (j : ℕ) : 0 ≤ oldSignedMaxTraceDepth P a j :=
    (old_signed_max_trace_depth_bounds P a hEll j).1
  unfold parentBoundaryBandMaxTraceHistory oldSignedMaxTraceHistory
  simp_rw [parent_history_physical_depth M P n height t ω]
  simp_rw [← ENNReal.ofReal_mul (pow_nonneg inverse_history_discount_range.1.le _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j) (hn j)) hs,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]

theorem parent_history_centered_history
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    parentBoundaryCommonCenteredMaxHistory M P n height t ω =
      ENNReal.ofReal (oldSignedMaxTraceHistory P
        (parentHistoryCenteredFrame M P n height t ω)) := by
  let a := parentHistoryCenteredFrame M P n height t ω
  let σ := Annealed.sigmaBar M n
  have hEll : IsEllipticFieldOn (M.nu / σ)
      (((M.nu / σ)^2 + (‖parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeCentered P n height t ω)‖ / σ)^2) / (M.nu / σ))
      (openCubeSet P) a := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1
      (parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeCentered P n height t ω))
  have hs := old_signed_max_trace_series_summable P a hEll
  have hn (j : ℕ) : 0 ≤ oldSignedMaxTraceDepth P a j :=
    (old_signed_max_trace_depth_bounds P a hEll j).1
  unfold parentBoundaryCommonCenteredMaxHistory oldSignedMaxTraceHistory
  simp_rw [parent_history_centered_depth M P n height t ω]
  simp_rw [← ENNReal.ofReal_mul (pow_nonneg inverse_history_discount_range.1.le _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j) (hn j)) hs,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]

end
end ASDExplicitGamma.Native
