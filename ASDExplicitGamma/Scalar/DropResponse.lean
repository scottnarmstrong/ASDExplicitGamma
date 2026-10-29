module

public import ASDExplicitGamma.Scalar.OldHessianTrialUnitIsotropy
public import ASDExplicitGamma.Scalar.TrueFrameNormalization
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldMatrixMean
public import ASDExplicitGamma.Main.PartialInsertion
public import ASDExplicitGamma.Variational.Subadditivity
public import ASDExplicitGamma.Model.Translation

/-! Response identifications for SC-ONE-SHELL-RECIPROCAL-DROP. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section

theorem drop_quad_integrable (M : ABKModel 2) (k : ℤ) (Q : TriadicCube 2) (e : Vec 2) :
    Integrable (fun ω => vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu k ω).toFun).lowerRight e))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hint (i j : Fin 2) : Integrable (fun ω => (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu k ω).toFun).lowerRight i j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    have h := upper_cell_old_framed_entry_integrable M k Q 1 (Sum.inr i) (Sum.inr j)
    simpa [frameMatrix, blockMatEntry] using h
  have hexp (X : Mat 2) : vecDot e (matVecMul X e) =
      e 0 * X 0 0 * e 0 + e 0 * X 0 1 * e 1 + e 1 * X 1 0 * e 0 + e 1 * X 1 1 * e 1 := by
    simp [vecDot, matVecMul, Fin.sum_univ_two]
    ring
  simp_rw [hexp]
  exact ((((hint 0 0).const_mul (e 0)).mul_const (e 0)).add
    (((hint 0 1).const_mul (e 0)).mul_const (e 1))).add
    (((hint 1 0).const_mul (e 1)).mul_const (e 0)) |>.add
    (((hint 1 1).const_mul (e 1)).mul_const (e 1))

/-- The expected directional lower-right block at label `k` is the physical inverse response. -/
theorem drop_quad_integral (M : ABKModel 2) (k : ℤ) (Q : TriadicCube 2) (e : Vec 2) :
    (∫ ω, vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu k ω).toFun).lowerRight e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = physicalInverseResponse M k Q e := by
  have hint (i j : Fin 2) : Integrable (fun ω => (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu k ω).toFun).lowerRight i j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    have h := upper_cell_old_framed_entry_integrable M k Q 1 (Sum.inr i) (Sum.inr j)
    simpa [frameMatrix, blockMatEntry] using h
  have hval (i j : Fin 2) : (∫ ω, (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu k ω).toFun).lowerRight i j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M k) (cubeSet Q)).lowerRight i j := by
    have h := upper_cell_old_framed_entry_integral M k Q 1 (Sum.inr i) (Sum.inr j)
    simpa [frameMatrix, blockMatEntry] using h
  have hexp (X : Mat 2) : vecDot e (matVecMul X e) =
      e 0 * X 0 0 * e 0 + e 0 * X 0 1 * e 1 + e 1 * X 1 0 * e 0 + e 1 * X 1 1 * e 1 := by
    simp [vecDot, matVecMul, Fin.sum_univ_two]
    ring
  unfold physicalInverseResponse
  simp_rw [hexp]
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  set L : Cutoff.CutoffSample 2 → Fin 2 → Fin 2 → ℝ := fun ω i j => (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu k ω).toFun).lowerRight i j with hL
  have h00 : Integrable (fun ω => e 0 * L ω 0 0 * e 0) μ :=
    ((hint 0 0).const_mul (e 0)).mul_const (e 0)
  have h01 : Integrable (fun ω => e 0 * L ω 0 1 * e 1) μ :=
    ((hint 0 1).const_mul (e 0)).mul_const (e 1)
  have h10 : Integrable (fun ω => e 1 * L ω 1 0 * e 0) μ :=
    ((hint 1 0).const_mul (e 1)).mul_const (e 0)
  have h11 : Integrable (fun ω => e 1 * L ω 1 1 * e 1) μ :=
    ((hint 1 1).const_mul (e 1)).mul_const (e 1)
  have hs1 : Integrable (fun ω => e 0 * L ω 0 0 * e 0 + e 0 * L ω 0 1 * e 1) μ := h00.add h01
  have hs2 : Integrable (fun ω => e 0 * L ω 0 0 * e 0 + e 0 * L ω 0 1 * e 1 +
      e 1 * L ω 1 0 * e 0) μ := hs1.add h10
  rw [integral_add hs2 h11, integral_add hs1 h10, integral_add h00 h01]
  have hval' (i j : Fin 2) : (∫ ω, L ω i j ∂μ) = (Book.Ch04.annealedBlockMatrix
      (Cutoff.coefficientCutoffLaw M k) (cubeSet Q)).lowerRight i j := hval i j
  simp only [integral_mul_const, integral_const_mul, hval']

/-- The heat average of the unit observable at an insertion time whose coefficient is the
cutoff coefficient at label `k` is `σ̄_m` times the physical inverse response at label `k`. -/
theorem drop_heat_eq_response (M : ABKModel 2) (m n k : ℤ) (t : ℝ) (e : Vec 2)
    (hc : ∀ ω, Model.partialInsertedCoefficient M m t ω = Cutoff.coefficientCutoff M.nu k ω) :
    oldHessianUnitHeat M n m e t =
      (Annealed.sigmaBar M m : ℝ) * physicalInverseResponse M k (originCube 2 n) e := by
  unfold oldHessianUnitHeat oldHessianUnitMatrix
  simp_rw [hc]
  simp_rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube, smul_matVecMul,
    vecDot_smul_right]
  rw [integral_const_mul, drop_quad_integral]

/-- Coarsening a cube lowers the expected lower-right block. -/
theorem drop_r_coarsen (M : ABKModel 2) (i : ℤ) (e : Vec 2) :
    physicalInverseResponse M i (originCube 2 (i + 129)) e ≤
      physicalInverseResponse M i (originCube 2 (i + 128)) e := by
  set Q : TriadicCube 2 := originCube 2 (i + 129) with hQ
  have hpath (ω : Cutoff.CutoffSample 2) :
      vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu i ω).toFun).lowerRight e) ≤
      descendantsAverage Q 1 (fun R => vecDot e (matVecMul (coarseBlockMatrix (cubeSet R)
        (Cutoff.coefficientCutoff M.nu i ω).toFun).lowerRight e)) := by
    have h := Variational.cutoff_coarse_matrix_subadditive M i Q 1 ω (0, e)
    have hz (x : Vec 2) : matVecMul (0 : Mat 2) x = 0 := by
      ext j
      simp only [matVecMul,Pi.zero_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero]
    simp only [descendantsAverageBlockMat, blockMatVecMul, blockVecDot, matVecMul_zero, hz,
      zero_add, add_zero, vecDot_zero_left] at h
    rw [vecDot_matVecMul_descendantsAverageMat] at h
    linarith
  classical
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  set D := descendantsAtDepth Q 1 with hD
  have hDne : D.Nonempty := by simpa [D] using descendantsAtDepth_nonempty Q 1
  have hcard : ((D.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hDne)
  have hscale (R : TriadicCube 2) (hR : R ∈ D) : R.scale = i + 128 := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [h]
    simp [hQ, originCube]
    ring
  have hresp (R : TriadicCube 2) (hR : R ∈ D) :
      physicalInverseResponse M i R e =
        physicalInverseResponse M i (originCube 2 (i + 128)) e := by
    unfold physicalInverseResponse
    rw [Model.annealedBlockMatrix_cube_eq_origin M i R,
      Model.annealedBlockMatrix_cube_eq_origin M i (originCube 2 (i + 128)), hscale R hR]
    rfl
  have hRint (R : TriadicCube 2) : Integrable (fun ω => vecDot e (matVecMul
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu i ω).toFun).lowerRight e)) μ :=
    drop_quad_integrable M i R e
  have havgInt : Integrable (fun ω => descendantsAverage Q 1 (fun R => vecDot e (matVecMul
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu i ω).toFun).lowerRight e))) μ := by
    unfold descendantsAverage
    exact (integrable_finset_sum _ (fun R _ => hRint R)).const_mul _
  have havgVal : (∫ ω, descendantsAverage Q 1 (fun R => vecDot e (matVecMul
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu i ω).toFun).lowerRight e)) ∂μ) =
      physicalInverseResponse M i (originCube 2 (i + 128)) e := by
    unfold descendantsAverage
    rw [integral_const_mul, integral_finset_sum _ (fun R _ => hRint R)]
    have hsum : (∑ R ∈ D, ∫ ω, vecDot e (matVecMul
        (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu i ω).toFun).lowerRight e) ∂μ) =
        ∑ R ∈ D, physicalInverseResponse M i (originCube 2 (i + 128)) e := by
      refine Finset.sum_congr rfl (fun R hR => ?_)
      rw [drop_quad_integral, hresp R hR]
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    field_simp
    rfl
  rw [← drop_quad_integral M i Q e, ← havgVal]
  exact integral_mono (drop_quad_integrable M i Q e) havgInt hpath

end
end ASDExplicitGamma.Scalar
