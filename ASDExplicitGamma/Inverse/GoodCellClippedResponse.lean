module

public import ASDExplicitGamma.Inverse.GoodCellResponse

/-! Identity-cell response comparison with the literal clipped matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The clipped pure-flux quadratic is exactly sigmaBar times the old
inverse-block quadratic whenever the actual old history is good. -/
theorem clipped_good_pure_flux_eq (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ)
    (τ : ℝ) (ω : Cutoff.CutoffSample 2) (hg : ω ∈ clippedCellGoodEvent M n Q τ) (v : Vec 2) :
    fullMatrixQuadratic (toFullBlockVec (0,v)) (clippedCellMatrix M n Q τ ω)=
      (Annealed.sigmaBar M n:ℝ)*dotProduct v ((coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu n ω).toFun).lowerRight.mulVec v) := by
  rw [clippedCellMatrix,Set.indicator_of_mem hg]
  change fullMatrixQuadratic (toFullBlockVec (0,v)) (toFullBlockMat
    (ASDExplicitGamma.Variational.frameMatrix (Annealed.sigmaBar M n:ℝ) _))=_
  rw [fullMatrixQuadratic_block,← lower_right_quadratic]
  simp only [ASDExplicitGamma.Variational.frameMatrix,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- Actual identity-cell energy is bounded by the same full old matrix
which enters the deterministic layer average and its centered positive error. -/
theorem good_cell_clipped_pure_flux_response (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    (Annealed.sigmaBar M (Q.scale+40):ℝ)*dotProduct v
      ((coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootEdelta r*fullMatrixQuadratic (toFullBlockVec (0,v))
        (clippedCellMatrix M (Q.scale+40) Q (rootTau r) ω) := by
  rw [clipped_good_pure_flux_eq M Q (Q.scale+40) _ ω (good_cell_raw_history M Q _ _ ω hgood)]
  have hh := mul_le_mul_of_nonneg_left
    (good_cell_pure_flux_response M Q r m J hn hm weights hw ω hgood v)
      (Annealed.sigmaBar_characterization M (Q.scale+40)).1.le
  simpa only [mul_left_comm] using hh

end
end ASDExplicitGamma.Inverse
