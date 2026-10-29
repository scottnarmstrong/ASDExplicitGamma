module

public import ASDExplicitGamma.Scalar.InverseHistoryLambda
public import ASDExplicitGamma.Variational.CubeResponse

/-! Local source identification: inverse history uses the actual lower-right coarse block. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational

/-- The source canonical inverse is the actual lower-right coarse block. -/
theorem inverse_history_lowerRight (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    sigmaStarInvCoarse (openCubeSet Q) a=(coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hConv := isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : 0<(MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have instInverseHistoryFiniteOpenVolume : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hConv.isFiniteMeasure_restrict_volume
  obtain ⟨R,sigma,compat,hA,_,_,_,_,_⟩ :=
    Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain hConv hEll hvol
  rw [cube_coarseMatrix_eq_open]
  exact (coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hA).symm

/-- Scaling a source inverse by its positive deterministic frame scales the genuine operator norm. -/
theorem inverse_history_matrixNorm_smul (A : Mat 2) (sigma : ℝ) (hsigma : 0≤sigma) :
    Book.Ch02.matrixNorm (sigma • A)=sigma*Book.Ch02.matrixNorm A := by
  simp only [Book.Ch02.matrixNorm,map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hsigma]

/-- Positive frame multiplication commutes with the actual finite maximum. -/
theorem inverse_history_finset_max_mul {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) (hc : 0<c) :
    Book.Ch02.finsetSupReal s (fun i => c*f i)=c*Book.Ch02.finsetSupReal s f := by
  apply le_antisymm (Book.Ch02.finsetSupReal_const_mul_le s hs hc.le f)
  have h := Book.Ch02.finsetSupReal_const_mul_le s hs (inv_nonneg.mpr hc.le) (fun i => c*f i)
  have he : (fun i => c⁻¹*(c*f i))=f := by
    funext i
    rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left h hc.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] using hh

/-- The depth maximum is exactly max_V ||sigma s_*^{-1}(V)||, as specified in TR-INV-HISTORY. -/
theorem inverse_history_framed_depth_max (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (sigma : ℝ) (hsigma : 0<sigma) (d : ℕ) :
    Book.Ch02.finsetSupReal (descendantsAtDepth Q d)
      (fun R => Book.Ch02.matrixNorm (sigma • (coarseBlockMatrix (cubeSet R) a).lowerRight))=
        sigma*lemmaVInverseDepthMax Q a d := by
  unfold lemmaVInverseDepthMax
  rw [← inverse_history_finset_max_mul _ (descendantsAtDepth_nonempty Q d) _ sigma hsigma]
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  rw [inverse_history_matrixNorm_smul _ sigma hsigma.le,
    inverse_history_lowerRight R a (hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR))]

end ASDExplicitGamma.Scalar
