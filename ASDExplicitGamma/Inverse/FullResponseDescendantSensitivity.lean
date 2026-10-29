module

public import ASDExplicitGamma.Inverse.FullResponseCellSensitivity
public import ASDExplicitGamma.Inverse.DescendantResponse

/-! The centered full-pair sensitivity estimate propagates from a good
parent to every contained cube, with the original completed-label frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

/-- A good parent controls the centered full response matrix on every
contained descendant. The centering uses that descendant's actual wave mean;
the exponential factor remains the parent's sensitivity cap. -/
theorem good_parent_descendant_centered_full_pair_response (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (r : RootRow) (m J : ℤ)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q) :
    let n := Q.scale + 40
    let a := sourceBandWeights m weights
    let k := oldResponseCoefficient Q n ω
    let kH := laterResponseCoefficient Q n J a ω
    let h := laterBandW2 Q n J a ω
    let kR := sensitivityResponseCoefficientRestrict k hR
    let kHR := sensitivityResponseCoefficientRestrict kH hR
    let hR' := h.restrict hR
    let μ := cubeAverage R hR'.value.toFun
    let kHR0 := kHR + BoundedContinuousFunction.const (closure (openCubeSet R)) (-μ)
    ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet R)
          (sensitivityBaseRegField M.nu
            (sensitivityResponseCoefficientPath kR kHR0 1)).toFun) P) ≤
        rootEdelta r * blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (cubeSet R)
            (Cutoff.coefficientCutoff M.nu n ω).toFun) P) := by
  dsimp only
  let n := Q.scale + 40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  let kR := sensitivityResponseCoefficientRestrict k hR
  let kHR := sensitivityResponseCoefficientRestrict kH hR
  let hR' := h.restrict hR
  let μ := cubeAverage R hR'.value.toFun
  let kHR0 := kHR + BoundedContinuousFunction.const (closure (openCubeSet R)) (-μ)
  let x := sensitivityDsharp R hR' *
    sensitivityPathLambdaInverse M.nu M.nu_pos kR kHR (1/4) 0
  have ha := source_band_weights_bounds n m J weights hw
  have hgate := good_cell_sensitivity_ode_gate M Q r ω hgood J a ha
  have hdesc : x ≤ sensitivityDsharp Q h *
      sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0 :=
    sensitivityDsharp_mul_descendant_lambda_inv_le M.nu M.nu_pos k kH h hR
      (1/4) (by norm_num) le_rfl 0
  have hx := hdesc.trans (good_cell_sensitivity_size_bound M Q (rootTau r)
    (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))
    (by cases r <;> norm_num [rootTau])
    (ASDExplicitGamma.Gaussian.wave_gate_eta_pos (rootWaveTuple r)).le
    ω hgood J a ha)
  have hquarter := hx.trans (root_sensitivity_gate_quarter r)
  have hsmall : sensitivityB2 * sensitivityDsharp R hR' *
      sensitivityPathLambdaInverse M.nu M.nu_pos kR kHR (1/4) 0 < 1 := by
    have hB0 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
    have hh := mul_le_mul_of_nonneg_left hquarter hB0
    have hB := sensitivityB2_lt_45016
    rw [mul_assoc]
    change sensitivityB2*x < 1
    nlinarith only [hh, hB]
  have hloc : sensitivityDsharp R hR' *
      sensitivityPathLambdaInverse M.nu M.nu_pos kR kHR (1/4) 0 ≤ sensitivityCloc :=
    hquarter.trans (by norm_num [sensitivityCloc])
  have hrep := later_response_coefficient_represents Q n J a ω
  have hrepR := sensitivityResponseCoefficientRestrict_represents kH h hrep hR
  have hode := sensitivity_coarse_sensitivity_ode_caps M.nu M.nu_pos kR kHR hR' hrepR
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 1/4) hsmall hloc
  have hcenter := sensitivity_book_matrix_eq R M.nu M.nu_pos
    (sensitivityResponseCoefficientPath kR kHR0 1)
  have hold := sensitivity_restrict_matrix_eq M.nu M.nu_pos k hR
  have hold' : Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R M.nu M.nu_pos kR) =
      coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun := by
    calc
      _ = coarseBlockMatrix (cubeSet R) (sensitivityBaseRegField M.nu k).toFun := hold
      _ = _ := by
        rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
          coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
        apply coarseBlockMatrix_congr_of_ae_eq
        filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with z hz
        exact old_response_coefficient_represents M Q n ω
          (openCubeSet_subset_of_mem_descendantsAtDepth hR hz)
  intro P
  have hquad := hode.2.2 P
  rw [sensitivityBlockScale_quadratic] at hquad
  change (1/2:ℝ) * blockVecDot P
      (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R M.nu M.nu_pos
            (sensitivityResponseCoefficientPath kR kHR0 1))) P) ≤
    (1/2:ℝ) * (Real.exp (sensitivityCA*x) * blockVecDot P
      (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R M.nu M.nu_pos kR)) P)) at hquad
  rw [hcenter, hold'] at hquad
  have hnonneg : 0 ≤ blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun) P) := by
    obtain ⟨Lam, hEll⟩ :=
      ASDExplicitGamma.Variational.cutoff_isEllipticFieldOn_cube M n ω R
    have hpair := history_framed_pair_bounds R _ M.nu_pos hEll 1 one_pos
    have hpos := hpair.1 P.1 P.2
    have hneg := hpair.2 P.1 P.2
    have hframe : frameMatrix 1
        (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun) =
        coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun := by
      cases coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun
      simp [frameMatrix]
    rw [hframe] at hpos hneg
    rcases le_total 0 (vecDot P.1 P.2) with h | h
    · exact (by positivity : 0 ≤ 2 * vecDot P.1 P.2).trans hpos
    · have hnonpos : 0 ≤ -2 * vecDot P.1 P.2 := by nlinarith only [h]
      exact hnonpos.trans hneg
  have hCA : 0 ≤ sensitivityCA := by norm_num [sensitivityCA]
  have hfactor : Real.exp (sensitivityCA*x) ≤ rootEdelta r := by
    apply Real.exp_le_exp.mpr
    have hcap := mul_le_mul_of_nonneg_left hx hCA
    change sensitivityCA*x ≤ (17444/10000:ℝ)*(1+rootTau r)*
      (10*ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))
    convert hcap using 1
    dsimp only [x, sensitivityCA]
    ring
  have hfactor' := mul_le_mul_of_nonneg_right hfactor hnonneg
  nlinarith only [hquad, hfactor']

end
end ASDExplicitGamma.Inverse
