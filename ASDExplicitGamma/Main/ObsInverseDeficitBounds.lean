module

public import ASDExplicitGamma.Main.HotInverseIdent
public import ASDExplicitGamma.Main.HotPatchBank
public import ASDExplicitGamma.Main.InverseDeficitHistoryBound

/-! MA-INVERSE-DEFICIT at observer cubes, step 1: the actual inverse trace on the observer root
is nonnegative and at most `2 B*`, with `B*` the global observer-root inverse maximum. The proof
is source §3 (3.2): coarse subadditivity (depth monotonicity of `lemmaVInverseDepthMax`) and
`hot_cell_history_le_bstar` for the depth `hobs+5` cells. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
  ASDExplicitGamma.Native ASDExplicitGamma.Model
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Pathwise, the observer inverse trace is nonnegative and at most `2 B*`. -/
theorem obs_inverse_trace_bounds (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : CutoffSample 2) :
    let n := m + (hobs : ℤ)
    let Q := originCube 2 n
    let σ : ℝ := Annealed.sigmaBar M m
    let x := modelInsertedScalar (closure (cubeSet Q)) m t
    0 ≤ mainInverseObservable n M.nu σ (x ω) ∧
      mainInverseObservable n M.nu σ (x ω) ≤ 2 * mixedBridgeBstar M m t ω := by
  intro n Q σ x
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let xω := x ω
  let k := pureFluxOpenResponseRestriction n xω
  let kClosed : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ xω
  let P := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu kClosed)
  let af := responseFramePlanarCoefficientField M.nu σ k
  let A := coarseBlockMatrix (cubeSet Q) af
  have hEll : IsEllipticFieldOn (M.nu / σ) (((M.nu / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (M.nu / σ))
      (openCubeSet Q) af :=
    responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) M.nu σ
      M.nu_pos hσ k
  have hframeOpen := hot_open_frame_coarse n M.nu σ M.nu_pos hσ xω
  have hAopen : A = frameMatrix σ P := by
    change coarseBlockMatrix (cubeSet Q) af = _
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
    exact hframeOpen
  have hdepthZero : ∀ R : TriadicCube 2, lemmaVInverseDepthMax R af 0 =
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) af) := by
    intro R
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero, Book.Ch02.finsetSupReal,
      Finset.coe_singleton, Set.image_singleton, csSup_singleton]
  have hRootZero : lemmaVInverseDepthMax Q af 0 = Book.Ch02.matrixNorm A.lowerRight := by
    rw [hdepthZero]
    exact congrArg Book.Ch02.matrixNorm (Scalar.inverse_history_lowerRight Q af hEll)
  have htraceNorm : Matrix.trace A.lowerRight ≤ 2 * Book.Ch02.matrixNorm A.lowerRight := by
    let C := A.lowerRight
    have h0 := (le_abs_self (C 0 0)).trans (clipped_matrix_entry_abs_le_norm C 0 0)
    have h1 := (le_abs_self (C 1 1)).trans (clipped_matrix_entry_abs_le_norm C 1 1)
    have h0' : C 0 0 ≤ Book.Ch02.matrixNorm C := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h0
    have h1' : C 1 1 ≤ Book.Ch02.matrixNorm C := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h1
    simp only [Matrix.trace, Fin.sum_univ_two]
    dsimp [C]
    nlinarith only [h0', h1']
  have hphysicalEll := responsePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) M.nu M.nu_pos kClosed
  have hphysicalPos := coarseBlockMatrix_posDef M.nu_pos hphysicalEll
  have hdiag0 : 0 < P.lowerRight 0 0 := by
    simpa only [toFullBlockMat] using hphysicalPos.diag_pos (i := Sum.inr (0 : Fin 2))
  have hdiag1 : 0 < P.lowerRight 1 1 := by
    simpa only [toFullBlockMat] using hphysicalPos.diag_pos (i := Sum.inr (1 : Fin 2))
  have hnonneg : 0 ≤ mainInverseObservable n M.nu σ xω := by
    unfold mainInverseObservable
    change 0 ≤ σ * Matrix.trace P.lowerRight
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
    exact mul_nonneg hσ.le (add_nonneg hdiag0.le hdiag1.le)
  have hmain : mainInverseObservable n M.nu σ xω = Matrix.trace A.lowerRight := by
    unfold mainInverseObservable
    rw [hAopen]
    simp [frameMatrix, Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul, P]
    ring
  refine ⟨hnonneg, ?_⟩
  rw [hmain]
  have hmono : Monotone (lemmaVInverseDepthMax Q af) :=
    monotone_nat_of_le_succ (fun j => lemmaVInverseDepthMax_le_succ Q hEll j)
  have hD : lemmaVInverseDepthMax Q af (hobs + 5) ≤ mixedBridgeBstar M m t ω := by
    unfold lemmaVInverseDepthMax
    refine Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q (hobs + 5)) ?_
    intro R hR
    have hEllR : IsEllipticFieldOn (M.nu / σ) (((M.nu / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (M.nu / σ))
        (openCubeSet R) af :=
      hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have h0 := bank_inverse_depth_zero_le_history R af hEllR
      (show 1 < (3 : ℝ) ^ (1 / 4 : ℝ) from Real.one_lt_rpow (by norm_num) (by norm_num))
    have hcell := hot_cell_history_le_bstar M m hobs h40 t ht ω R hR
    rw [← hdepthZero R]
    exact h0.trans hcell
  calc Matrix.trace A.lowerRight ≤ 2 * Book.Ch02.matrixNorm A.lowerRight := htraceNorm
    _ = 2 * lemmaVInverseDepthMax Q af 0 := by rw [hRootZero]
    _ ≤ 2 * lemmaVInverseDepthMax Q af (hobs + 5) :=
      mul_le_mul_of_nonneg_left (hmono (Nat.zero_le _)) (by norm_num)
    _ ≤ 2 * mixedBridgeBstar M m t ω := mul_le_mul_of_nonneg_left hD (by norm_num)

end

end ASDExplicitGamma.Main
