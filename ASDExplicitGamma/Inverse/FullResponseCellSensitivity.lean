module

public import ASDExplicitGamma.Inverse.SensitivityResponse
public import ASDExplicitGamma.Inverse.GoodCellResponse
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Inverse.FullResponseCellCoefficient

/-! Full-pair sensitivity control for the centered later response on a good
physical cell. The mean skew remains for the separate trace shear payment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

/-- On a good cell, the centered full response matrix is dominated in every
paired loading by the actual old matrix, with the source `E_delta` factor. -/
theorem good_cell_centered_full_pair_response (M : ABKModel 2)
    (Q : TriadicCube 2) (r : RootRow) (m J : ℤ)
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
    let kH0 := kH + BoundedContinuousFunction.const (closure (openCubeSet Q))
      (-(cubeAverage Q h.value.toFun))
    ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q)
          (sensitivityBaseRegField M.nu
            (sensitivityResponseCoefficientPath k kH0 1)).toFun) P) ≤
        rootEdelta r * blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu n ω).toFun) P) := by
  dsimp only
  let n := Q.scale + 40
  let a := sourceBandWeights m weights
  let k := oldResponseCoefficient Q n ω
  let kH := laterResponseCoefficient Q n J a ω
  let h := laterBandW2 Q n J a ω
  let kH0 := kH + BoundedContinuousFunction.const (closure (openCubeSet Q))
    (-(cubeAverage Q h.value.toFun))
  let x := sensitivityDsharp Q h *
    sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0
  have ha := source_band_weights_bounds n m J weights hw
  have hgate := good_cell_sensitivity_ode_gate M Q r ω hgood J a ha
  have hs : sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse M.nu M.nu_pos k kH (1/4) 0 < 1 := by
    simpa only [mul_assoc] using hgate.1
  have hrep := later_response_coefficient_represents Q n J a ω
  have hode := sensitivity_coarse_sensitivity_ode_caps M.nu M.nu_pos k kH h hrep
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 1/4) hs hgate.2
  have hx := good_cell_sensitivity_size_bound M Q (rootTau r)
    (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))
    (by cases r <;> norm_num [rootTau])
    (ASDExplicitGamma.Gaussian.wave_gate_eta_pos (rootWaveTuple r)).le
    ω hgood J a ha
  have hCA : 0 ≤ sensitivityCA := by norm_num [sensitivityCA]
  have hcap := mul_le_mul_of_nonneg_left hx hCA
  have hfactor : Real.exp (sensitivityCA * x) ≤ rootEdelta r := by
    apply Real.exp_le_exp.mpr
    change sensitivityCA * x ≤ (17444 / 10000 : ℝ) *
      (1 + rootTau r) * (10 *
        ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))
    convert hcap using 1
    dsimp only [x, sensitivityCA]
    ring
  have hcenter := sensitivity_book_matrix_eq Q M.nu M.nu_pos
    (sensitivityResponseCoefficientPath k kH0 1)
  have hold := old_sensitivity_matrix_eq M Q n ω
  intro P
  have hquad := hode.2.2 P
  rw [sensitivityBlockScale_quadratic] at hquad
  change (1 / 2 : ℝ) * blockVecDot P
      (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q M.nu M.nu_pos
            (sensitivityResponseCoefficientPath k kH0 1))) P) ≤
    (1 / 2 : ℝ) * (Real.exp (sensitivityCA * x) *
      blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q M.nu M.nu_pos k)) P)) at hquad
  rw [hcenter, hold] at hquad
  have hnonneg : 0 ≤ blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun) P) := by
    obtain ⟨Lam, hEll⟩ :=
      ASDExplicitGamma.Variational.cutoff_isEllipticFieldOn_cube M n ω Q
    have hpair := history_framed_pair_bounds Q _ M.nu_pos hEll 1 one_pos
    have hpos := hpair.1 P.1 P.2
    have hneg := hpair.2 P.1 P.2
    have hframe : frameMatrix 1
        (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun) =
        coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun := by
      cases coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun
      simp [frameMatrix]
    rw [hframe] at hpos hneg
    rcases le_total 0 (vecDot P.1 P.2) with h | h
    · have hnonneg' : 0 ≤ 2 * vecDot P.1 P.2 := by positivity
      exact hnonneg'.trans hpos
    · have hnonpos : 0 ≤ -2 * vecDot P.1 P.2 := by nlinarith only [h]
      exact hnonpos.trans hneg
  have hfactor' := mul_le_mul_of_nonneg_right hfactor hnonneg
  nlinarith only [hquad, hfactor']

end
end ASDExplicitGamma.Inverse
