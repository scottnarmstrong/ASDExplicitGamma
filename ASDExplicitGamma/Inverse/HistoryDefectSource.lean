module

public import ASDExplicitGamma.Inverse.HistoryDefectMatrix
public import ASDExplicitGamma.Inverse.HistoryTrace

/-! Source ellipticity supplies the pairing and symmetry facts for the defect.
The Mu representation is reused from TraceDefect; no duality premise is added. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3

/-- Scalar framing preserves the actual coarse symmetry. -/
theorem history_frame_symmetric (sigma : ℝ) (A : BlockMat 2) (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (Variational.frameMatrix sigma A) := by
  intro α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      simpa only [Variational.frameMatrix,blockMatEntry,Matrix.smul_apply,smul_eq_mul] using
        congrArg (fun x : ℝ => sigma⁻¹*x) (hA (Sum.inl i) (Sum.inl j))
    | inr j => exact hA (Sum.inl i) (Sum.inr j)
  | inr i =>
    cases β with
    | inl j => exact hA (Sum.inr i) (Sum.inl j)
    | inr j =>
      simpa only [Variational.frameMatrix,blockMatEntry,Matrix.smul_apply,smul_eq_mul] using
        congrArg (fun x : ℝ => sigma*x) (hA (Sum.inr i) (Sum.inr j))

theorem history_coarse_symmetric (Q : TriadicCube 2) (a : CoeffField 2) {nu Lam : ℝ}
    (hEll : IsEllipticFieldOn nu Lam (cubeSet Q) a) :
    IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a) := by
  have hConv := isOpenBoundedConvexDomain_openCubeSet Q
  have instFiniteOpen : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨sigma,hA,_,_,_,_,_,_⟩ := Variational.exists_energyMap_coarseData hConv
    (hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)) hvol
  have hc := (isCoarseBlockMatrix_coarseBlockMatrix ⟨_,hA⟩).1
  simpa only [Variational.cube_coarseMatrix_eq_open] using hc

/-- Both signs of the pairing follow from the actual admissible variational problems. -/
theorem history_framed_pair_bounds (Q : TriadicCube 2) (a : CoeffField 2) {nu Lam : ℝ}
    (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam (cubeSet Q) a)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    (∀ p q : Vec 2, 2*vecDot p q ≤ blockVecDot (p,q)
      (blockMatVecMul (Variational.frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a)) (p,q))) ∧
    (∀ p q : Vec 2, -2*vecDot p q ≤ blockVecDot (p,q)
      (blockMatVecMul (Variational.frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a)) (p,q))) := by
  have instFiniteCube : IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    ((isBounded_cubeSet Q).isBoundedDomain).isFiniteMeasure_restrict_volume
  have hSob : IsSobolevRegularDomain (cubeSet Q) := ⟨measurableSet_cubeSet Q,(isBounded_cubeSet Q).isBoundedDomain⟩
  have hvol : (volume (cubeSet Q)).toReal ≠ 0 := by rw [volume_cubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  have hPair {a' : CoeffField 2} (hE : IsEllipticFieldOn nu Lam (cubeSet Q) a') (P : BlockVec 2) :
      vecDot P.1 P.2 ≤ Mu (cubeSet Q) P a' :=
    IsBlockMuAdmissible.mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain hSob hE hvol
  have hs : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.mpr hsigma).ne'
  have hs2 : (Real.sqrt sigma)^2 = sigma := Real.sq_sqrt hsigma.le
  have hdot (p q : Vec 2) : vecDot ((Real.sqrt sigma)⁻¹ • p) (Real.sqrt sigma • q) = vecDot p q := by
    rw [vecDot_smul_left,vecDot_smul_right]
    field_simp [hs]
  have hmu (P : BlockVec 2) :
      Mu (cubeSet Q) ((Real.sqrt sigma)⁻¹ • P.1,Real.sqrt sigma • P.2) a =
        (1/2 : ℝ)*blockVecDot P (blockMatVecMul (Variational.frameMatrix sigma
          (coarseBlockMatrix (cubeSet Q) a)) P) := by
    rw [Variational.mu_eq_half_coarseBlockMatrix_elliptic_triCube hnu hEll,
      Variational.frame_load_quadratic _ P _ hs,hs2]
  constructor
  · intro p q
    have h := hPair hEll ((Real.sqrt sigma)⁻¹ • p,Real.sqrt sigma • q)
    rw [hmu (p,q),hdot] at h
    linarith only [h]
  · intro p q
    have h := hPair (isEllipticFieldOn_adjointCoeffField hEll)
      (blockVecFlipFlux ((Real.sqrt sigma)⁻¹ • p,Real.sqrt sigma • q))
    rw [Mu_adjointCoeffField_flipFlux] at h
    simp only [blockVecFlipFlux,vecDot_neg_right] at h
    rw [hmu (p,q),hdot] at h
    linarith only [h]

/-- The source defect is PSD at every sample in its genuine true frame. -/
theorem history_cutoff_defect_posSemidef (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    (historyDefectMatrix (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun))).PosSemidef := by
  obtain ⟨Lam,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M n ω Q
  have hpair := history_framed_pair_bounds Q _ M.nu_pos hEll _ (Annealed.sigmaBar_characterization M n).1
  exact history_defect_posSemidef _
    (history_frame_symmetric _ _ (history_coarse_symmetric Q _ hEll)) hpair.1 hpair.2

noncomputable def historyOperatorDefect (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
    (historyDefectMatrix (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)))‖

/-- Honest Euclidean operator norm, dominated by the exact frozen trace defect. -/
theorem history_operator_defect_le_trace (M : ABKModel 2) (n : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    historyOperatorDefect M n Q ω ≤ historyTrace M n Q ω := by
  have h := Book.Ch05.Section56.fullBlockOperatorNorm_le_trace_of_posSemidef _
    (history_cutoff_defect_posSemidef M n Q ω)
  rw [history_defect_trace] at h
  exact h

end ASDExplicitGamma.Inverse
