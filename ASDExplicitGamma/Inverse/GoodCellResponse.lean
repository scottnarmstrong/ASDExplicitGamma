module

public import ASDExplicitGamma.Inverse.SensitivityResponse

/-! Actual good-cell response comparison with the source exponential cap. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The old sensitivity matrix is the completed-cutoff matrix. -/
theorem old_sensitivity_matrix_eq (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q M.nu M.nu_pos (oldResponseCoefficient Q n ω)) =
        coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun := by
  rw [sensitivity_book_matrix_eq,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact old_response_coefficient_represents M Q n ω hx

/-- The uncentered time-one Book matrix is the full-UV attenuated matrix. -/
theorem attenuated_sensitivity_matrix_eq (M : ABKModel 2) (Q : TriadicCube 2)
    (n m J : ℤ) (hn : n ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q M.nu M.nu_pos
      (oldResponseCoefficient Q n ω+laterResponseCoefficient Q n J (sourceBandWeights m weights) ω)) =
        coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω) := by
  rw [sensitivity_book_matrix_eq,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact sensitivity_path_represents_attenuated M Q n m J hn hm weights ω hx

/-- Nonnegativity of every actual old pure-flux quadratic form. -/
theorem old_pure_flux_nonneg (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) (v : Vec 2) :
    0 ≤ dotProduct v ((coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun).lowerRight.mulVec v) := by
  obtain ⟨Lam,hEll⟩ := ASDExplicitGamma.Variational.cutoff_isEllipticFieldOn_cube M n ω Q
  have hh := (history_framed_pair_bounds Q _ M.nu_pos hEll 1 one_pos).1 0 v
  rw [← lower_right_quadratic] at hh
  simpa [ASDExplicitGamma.Variational.frameMatrix,vecDot] using hh

/-- The good-cell comparison for the actual full-UV target, with arbitrary
deterministic attenuation and the source E_delta. All ODE inputs are proved
from the literal good-cell event. The statement is uniform in the flux load. -/
theorem good_cell_pure_flux_response (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    dotProduct v ((coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootEdelta r*dotProduct v ((coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu (Q.scale+40) ω).toFun).lowerRight.mulVec v) := by
  let n := Q.scale+40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  have ha := source_band_weights_bounds n m J weights hw
  have hgate := good_cell_sensitivity_ode_gate M Q r ω hgood J a ha
  have hs : sensitivityB2*sensitivityDsharp Q h*sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0 < 1 := by
    simpa only [mul_assoc] using hgate.1
  have hh := sensitivity_pure_flux_upper Q M.nu M.nu_pos k kH h
    (later_response_coefficient_represents Q n J a ω) hs hgate.2 v
  change dotProduct v ((Book.Ch02.coarseBlockMatrix _ (sensitivityBookCoeffOn Q M.nu M.nu_pos
    (oldResponseCoefficient Q n ω+laterResponseCoefficient Q n J a ω))).lowerRight.mulVec v) ≤ _ at hh
  rw [attenuated_sensitivity_matrix_eq M Q n m J hn hm weights ω,
    old_sensitivity_matrix_eq M Q n ω] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (old_pure_flux_nonneg M Q n ω v)
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hη := (ASDExplicitGamma.Gaussian.wave_gate_eta_pos (rootWaveTuple r)).le
  have hx := good_cell_sensitivity_size_bound M Q _ _ ht hη ω hgood J a ha
  have hCA : 0 ≤ sensitivityCA := by norm_num [sensitivityCA]
  have hcap := mul_le_mul_of_nonneg_left hx hCA
  change sensitivityCA*(sensitivityDsharp Q h*sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0) ≤ _
  convert hcap using 1
  unfold sensitivityCA
  ring

end
end ASDExplicitGamma.Inverse
