module

public import ASDExplicitGamma.Inverse.GoodCellResponse

/-! The actual good-parent sensitivity estimate on every contained descendant.
The descendant inverse-lambda comparison discharges the domain gate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- Restriction of a sensitivity representative leaves its genuine local
coarse matrix unchanged. Only values on the descendant matter. -/
theorem sensitivity_restrict_matrix_eq {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν (sensitivityResponseCoefficientRestrict k hR)) =
        coarseBlockMatrix (cubeSet R) (sensitivityBaseRegField ν k).toFun := by
  rw [sensitivity_book_matrix_eq,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [sensitivityResponseCoefficientRestrict_extension_ae k hR] with x hx
  change responsePlanarCoefficient (ν/1) (_/1)=responsePlanarCoefficient (ν/1) (_/1)
  rw [hx]

/-- A size cap in the exact source row implies its E_delta exponential cap. -/
theorem root_sensitivity_exponential_le (r : RootRow) {x : ℝ}
    (hx : x ≤ 2*(1+rootTau r)*(10*ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) :
    Real.exp (sensitivityCA*x) ≤ rootEdelta r := by
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ sensitivityCA := by norm_num [sensitivityCA]
  have hh := mul_le_mul_of_nonneg_left hx hc
  convert hh using 1
  unfold sensitivityCA
  ring

/-- Every actual descendant of a good parent satisfies the same uncentered
pure-flux response cap, in its parent's old coefficient. The old label stays
fixed while taking descendants. No descendant good-event premise is needed. -/
theorem good_parent_descendant_pure_flux_response (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    dotProduct v ((coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootEdelta r*dotProduct v ((coarseBlockMatrix (cubeSet R)
        (Cutoff.coefficientCutoff M.nu (Q.scale+40) ω).toFun).lowerRight.mulVec v) := by
  let n := Q.scale+40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  let kr := sensitivityResponseCoefficientRestrict k hR
  let kHr := sensitivityResponseCoefficientRestrict kH hR
  let x := sensitivityDsharp R (h.restrict hR)*sensitivityPathLambdaInverse M.nu M.nu_pos kr kHr (1/4) 0
  have ha := source_band_weights_bounds n m J weights hw
  have hdesc : x ≤ sensitivityDsharp Q h*sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0 :=
    sensitivityDsharp_mul_descendant_lambda_inv_le M.nu M.nu_pos k kH h hR (1/4)
      (by norm_num) le_rfl 0
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hη := (ASDExplicitGamma.Gaussian.wave_gate_eta_pos (rootWaveTuple r)).le
  have hx := hdesc.trans (good_cell_sensitivity_size_bound M Q _ _ ht hη ω hgood J a ha)
  have hquarter := hx.trans (root_sensitivity_gate_quarter r)
  have hsmall : sensitivityB2*sensitivityDsharp R (h.restrict hR)*
      sensitivityPathLambdaInverse M.nu M.nu_pos kr kHr (1/4) 0 < 1 := by
    have hB0 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
    have hh := mul_le_mul_of_nonneg_left hquarter hB0
    have hB := sensitivityB2_lt_45016
    rw [mul_assoc]
    change sensitivityB2*x < 1
    nlinarith only [hh,hB]
  have hloc : x ≤ sensitivityCloc := hquarter.trans (by norm_num [sensitivityCloc])
  have hh := sensitivity_pure_flux_upper R M.nu M.nu_pos kr kHr (h.restrict hR)
    (sensitivityResponseCoefficientRestrict_represents kH h
      (later_response_coefficient_represents Q n J a ω) hR) hsmall hloc v
  have hadd : kr+kHr=sensitivityResponseCoefficientRestrict (k+kH) hR := by ext z; rfl
  rw [hadd,sensitivity_restrict_matrix_eq M.nu M.nu_pos (k+kH) hR,
    sensitivity_restrict_matrix_eq M.nu M.nu_pos k hR] at hh
  have hnew : coarseBlockMatrix (cubeSet R) (sensitivityBaseRegField M.nu (k+kH)).toFun =
      coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with z hz
    exact sensitivity_path_represents_attenuated M Q n m J hn hm weights ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hz)
  have hold : coarseBlockMatrix (cubeSet R) (sensitivityBaseRegField M.nu k).toFun =
      coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with z hz
    exact old_response_coefficient_represents M Q n ω
      (openCubeSet_subset_of_mem_descendantsAtDepth hR hz)
  rw [hnew,hold] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (root_sensitivity_exponential_le r hx)
    (old_pure_flux_nonneg M R n ω v))

end
end ASDExplicitGamma.Inverse
