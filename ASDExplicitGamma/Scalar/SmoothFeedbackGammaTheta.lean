module

public import ASDExplicitGamma.Inverse.MixedBridgeDirectionalLocalTheta
public import ASDExplicitGamma.Main.EnvelopeXILocalTheta
public import ASDExplicitGamma.Main.EnvelopeXIActual
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaCovariance
public import ASDExplicitGamma.Scalar.SmoothFeedbackDirectionalHistory
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaMeasurability
public import ASDExplicitGamma.Scalar.SmoothFeedbackRawProxyTheta

/-! The accepted local OLD-Theta row pays the actual directional Gamma trace
at the centered source cell, preserving the planar half-trace factor. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Inverse ASDExplicitGamma.Main
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Algsuperdiff.Section3
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- At zero insertion, the OLD-frame directional Gram trace is paid by the
actual local `OLD-Theta` carrier with coefficient one. -/
theorem smooth_feedback_directional_gamma_trace_le_local_old_theta
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (Q : TriadicCube 2) (hQ : Q ∈ descendantsAtDepth (originCube 2 m) 5)
    (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellDirectionalGammaTrace M m Q ω ≤
      mixedOldTheta M m Q 0 ω := by
  have hRaw := smooth_feedback_cell_raw_proxy_le_local_old_theta
    M hγ m Q hQ ω
  have hGamma := smooth_feedback_directional_gamma_trace_le_raw_trace_proxy
    M m Q ω
  calc
    _ ≤ rawWeakTraceProxy
        (fun j => lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (oldCutoffSkewCoefficient m Q ω)) j)
        (fun j => descendantsAverage Q j (fun R =>
          traceDefect (openCubeSet R)
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m Q ω)) 1)) := by
      exact hGamma
    _ ≤ mixedOldTheta M m Q 0 ω := by
      exact hRaw

private theorem smooth_feedback_gamma_psd_entry_norm_le_trace
    {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hN : Matrix.PosSemidef N) (hSym : ∀ i j, N i j = N j i)
    (i j : Fin 2) : ‖N i j‖ ≤ Matrix.trace N := by
  have h00 : 0 ≤ N 0 0 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 0)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using h
  have h11 : 0 ≤ N 1 1 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 1)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using h
  have hplus : 0 ≤ N 0 0 + 2 * N 0 1 + N 1 1 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 0 + basisVec 1)
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] at h
    rw [hSym 1 0] at h
    nlinarith only [h]
  have hminus : 0 ≤ N 0 0 - 2 * N 0 1 + N 1 1 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 0 - basisVec 1)
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] at h
    rw [hSym 1 0] at h
    nlinarith only [h]
  have habs : |N 0 1| ≤ N 0 0 + N 1 1 := by
    rw [abs_le]
    constructor <;> nlinarith only [hplus, hminus, h00, h11]
  have hTrace : Matrix.trace N = N 0 0 + N 1 1 := by
    simp [Matrix.trace_fin_two]
  fin_cases i <;> fin_cases j
  · change ‖N 0 0‖ ≤ Matrix.trace N
    rw [Real.norm_eq_abs, abs_of_nonneg h00, hTrace]
    exact le_add_of_nonneg_right h11
  · change ‖N 0 1‖ ≤ Matrix.trace N
    rw [Real.norm_eq_abs, hTrace]
    exact habs
  · change ‖N 1 0‖ ≤ Matrix.trace N
    calc
      ‖N 1 0‖ = ‖N 0 1‖ := by rw [hSym 1 0]
      _ ≤ Matrix.trace N := by
        rw [Real.norm_eq_abs, hTrace]
        exact habs
  · change ‖N 1 1‖ ≤ Matrix.trace N
    rw [Real.norm_eq_abs, abs_of_nonneg h11, hTrace]
    exact le_add_of_nonneg_left h00

private theorem smooth_feedback_gamma_matrix_trace_eq_directional_trace
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    Matrix.trace
        (smoothFeedbackCellGammaMatrix M m Q ω) =
      smoothFeedbackCellDirectionalGammaTrace M m Q ω := by
  have h00 : smoothFeedbackCellGammaMatrix M m Q ω 0 0 =
      smoothFeedbackCellDirectionalGamma M m Q
        (basisVec 0) ω := by
    simpa [vecDot, matVecMul, Fin.sum_univ_two, basisVec] using
      (smooth_feedback_cell_gamma_matrix_quadratic_form M m
        Q ω (basisVec 0))
  have h11 : smoothFeedbackCellGammaMatrix M m Q ω 1 1 =
      smoothFeedbackCellDirectionalGamma M m Q
        (basisVec 1) ω := by
    simpa [vecDot, matVecMul, Fin.sum_univ_two, basisVec] using
      (smooth_feedback_cell_gamma_matrix_quadratic_form M m
        Q ω (basisVec 1))
  calc
    Matrix.trace (smoothFeedbackCellGammaMatrix M m Q ω) =
        smoothFeedbackCellGammaMatrix M m Q ω 0 0 +
          smoothFeedbackCellGammaMatrix M m Q ω 1 1 := by
      simp [Matrix.trace_fin_two]
    _ = smoothFeedbackCellDirectionalGamma M m Q
          (basisVec 0) ω +
        smoothFeedbackCellDirectionalGamma M m Q
          (basisVec 1) ω := by rw [h00, h11]
    _ = smoothFeedbackCellDirectionalGammaTrace M m Q ω := by
      simp [smoothFeedbackCellDirectionalGammaTrace, Fin.sum_univ_two]

/-- The expected directional Gamma is bounded by half the local OLD-Theta
expectation. The explicit matrix-integrability premise is the one discharged
by the local source profile in the node assembly. -/
theorem smooth_feedback_expected_directional_gamma_le_half_local_old_theta
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (Q : TriadicCube 2) (hQ : Q ∈ descendantsAtDepth (originCube 2 m) 5)
    (e : Vec 2)
    (hThetaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        mixedOldTheta M m (Q) 0 ω)
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    (∫ ω, smoothFeedbackCellDirectionalGamma M m
      (Q) e ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((∫ ω, mixedOldTheta M m (Q) 0 ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) / 2) * vecNormSq e := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hInt (i j : Fin 2) : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellGammaMatrix M m
          (Q) ω i j) μ := by
    have hMeas := smooth_feedback_gamma_matrix_entry_measurable M m Q i j
    refine hThetaInt.mono' hMeas.aestronglyMeasurable ?_
    filter_upwards with ω
    let N := smoothFeedbackCellGammaMatrix M m (Q) ω
    have hPSD : N.PosSemidef := by
      simpa [N] using smooth_feedback_cell_gamma_matrix_posSemidef
        M m (Q) ω
    have hSym : ∀ i j, N i j = N j i := by
      intro i j
      exact smooth_feedback_gamma_matrix_symmetric
        M m (Q) ω i j
    have hTraceEq : Matrix.trace N =
        smoothFeedbackCellDirectionalGammaTrace M m
          (Q) ω := by
      simpa [N] using smooth_feedback_gamma_matrix_trace_eq_directional_trace M m Q ω
    have hTraceNonneg : 0 ≤ Matrix.trace N := by
      rw [hTraceEq, smoothFeedbackCellDirectionalGammaTrace, Fin.sum_univ_two]
      exact add_nonneg
        (smooth_feedback_cell_directional_gamma_nonneg M m
          (Q) (basisVec 0) ω)
        (smooth_feedback_cell_directional_gamma_nonneg M m
          (Q) (basisVec 1) ω)
    calc
      ‖N i j‖ ≤ Matrix.trace N :=
        smooth_feedback_gamma_psd_entry_norm_le_trace hPSD hSym i j
      _ ≤ mixedOldTheta M m (Q) 0 ω := by
        calc
          Matrix.trace N = smoothFeedbackCellDirectionalGammaTrace M m
              (Q) ω := hTraceEq
          _ ≤ mixedOldTheta M m (Q) 0 ω :=
            smooth_feedback_directional_gamma_trace_le_local_old_theta
              M hγ m Q hQ ω
  have hGammaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellDirectionalGamma M m
          (Q) e ω) μ := by
    have hform (ω : Cutoff.CutoffSample 2) :
        smoothFeedbackCellDirectionalGamma M m
            (Q) e ω =
          ∑ i : Fin 2, ∑ j : Fin 2,
            e i * e j * smoothFeedbackCellGammaMatrix M m
              (Q) ω i j := by
      rw [← smooth_feedback_cell_gamma_matrix_quadratic_form]
      simp [vecDot, matVecMul, Fin.sum_univ_two]
      ring
    have hterm (i j : Fin 2) : Integrable
        (fun ω : Cutoff.CutoffSample 2 =>
          (e i * e j) * smoothFeedbackCellGammaMatrix M m
            (Q) ω i j) μ :=
      (hInt i j).const_mul (e i * e j)
    have hsum (i : Fin 2) : Integrable
        (fun ω : Cutoff.CutoffSample 2 => ∑ j : Fin 2,
          e i * e j * smoothFeedbackCellGammaMatrix M m
            (Q) ω i j) μ := by
      convert (hterm i 0).add (hterm i 1) using 1
      ext ω
      simp only [Fin.sum_univ_two]
      simp only [Pi.add_apply]
    have hsum2 : Integrable
        (fun ω : Cutoff.CutoffSample 2 => ∑ i : Fin 2, ∑ j : Fin 2,
          e i * e j * smoothFeedbackCellGammaMatrix M m
            (Q) ω i j) μ := by
      convert (hsum 0).add (hsum 1) using 1
      ext ω
      simp only [Fin.sum_univ_two]
      simp only [Pi.add_apply]
    exact hsum2.congr (Filter.Eventually.of_forall fun ω => (hform ω).symm)
  have h00 (ω : Cutoff.CutoffSample 2) :
      smoothFeedbackCellDirectionalGamma M m
        (Q) (basisVec 0) ω =
      smoothFeedbackCellGammaMatrix M m
        (Q) ω 0 0 := by
    rw [← smooth_feedback_cell_gamma_matrix_quadratic_form]
    simp [vecDot, matVecMul, basisVec]
  have h11 (ω : Cutoff.CutoffSample 2) :
      smoothFeedbackCellDirectionalGamma M m
        (Q) (basisVec 1) ω =
      smoothFeedbackCellGammaMatrix M m
        (Q) ω 1 1 := by
    rw [← smooth_feedback_cell_gamma_matrix_quadratic_form]
    simp [vecDot, matVecMul, basisVec]
  have hGamma00Int : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellDirectionalGamma M m
          (Q) (basisVec 0) ω) μ :=
    (hInt 0 0).congr (Filter.Eventually.of_forall fun ω => (h00 ω).symm)
  have hGamma11Int : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellDirectionalGamma M m
          (Q) (basisVec 1) ω) μ :=
    (hInt 1 1).congr (Filter.Eventually.of_forall fun ω => (h11 ω).symm)
  have hTraceInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellDirectionalGammaTrace M m
          (Q) ω) μ := by
    simp only [smoothFeedbackCellDirectionalGammaTrace, Fin.sum_univ_two]
    change Integrable (fun ω =>
      smoothFeedbackCellDirectionalGamma M m
        (Q) (basisVec 0) ω +
      smoothFeedbackCellDirectionalGamma M m
        (Q) (basisVec 1) ω) μ
    exact hGamma00Int.add hGamma11Int
  have hTracePoint (ω : Cutoff.CutoffSample 2) :
      smoothFeedbackCellDirectionalGammaTrace M m
          (Q) ω ≤
        mixedOldTheta M m (Q) 0 ω :=
    smooth_feedback_directional_gamma_trace_le_local_old_theta
      M hγ m Q hQ ω
  have hTraceIntegral :
      (∫ ω, smoothFeedbackCellDirectionalGammaTrace M m
        (Q) ω ∂μ) ≤
        ∫ ω, mixedOldTheta M m (Q) 0 ω ∂μ :=
    integral_mono hTraceInt hThetaInt hTracePoint
  have hHalf := smooth_feedback_expected_directional_gamma_half_trace_cell
    M m Q e hInt
  have hDiagIntegral :
      (∫ ω, smoothFeedbackCellDirectionalGammaTrace M m
        (Q) ω ∂μ) =
        (∫ ω, smoothFeedbackCellGammaMatrix M m
          (Q) ω 0 0 ∂μ) +
        ∫ ω, smoothFeedbackCellGammaMatrix M m
          (Q) ω 1 1 ∂μ := by
    simp only [smoothFeedbackCellDirectionalGammaTrace, Fin.sum_univ_two]
    change (∫ ω, smoothFeedbackCellDirectionalGamma M m
        (Q) (basisVec 0) ω +
      smoothFeedbackCellDirectionalGamma M m
        (Q) (basisVec 1) ω ∂μ) = _
    calc
      _ = (∫ ω, smoothFeedbackCellDirectionalGamma M m
            (Q) (basisVec 0) ω ∂μ) +
          ∫ ω, smoothFeedbackCellDirectionalGamma M m
            (Q) (basisVec 1) ω ∂μ :=
        integral_add hGamma00Int hGamma11Int
      _ = _ := congrArg₂ (fun x y => x + y)
        (integral_congr_ae (Filter.Eventually.of_forall h00))
        (integral_congr_ae (Filter.Eventually.of_forall h11))

  have hNorm : 0 ≤ vecNormSq e := vecNormSq_nonneg e
  have hNormEq : vecNormSq e = e 0 ^ 2 + e 1 ^ 2 := by
    simp [vecNormSq, vecDot, Fin.sum_univ_two]
    ring
  rw [hHalf]
  have hcoef :
      ((∫ ω, smoothFeedbackCellGammaMatrix M m
          (Q) ω 0 0 ∂μ) +
        ∫ ω, smoothFeedbackCellGammaMatrix M m
          (Q) ω 1 1 ∂μ) / 2 =
        (∫ ω, smoothFeedbackCellDirectionalGammaTrace M m
          (Q) ω ∂μ) / 2 := by
    rw [hDiagIntegral]
  rw [hcoef]
  rw [hNormEq]
  have hhalf := div_le_div_of_nonneg_right hTraceIntegral
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
  exact mul_le_mul_of_nonneg_right hhalf (by positivity)

/-- Integrability of the directional Gamma on a depth-five source cell, from the
integrability of its local OLD Theta. -/
theorem smooth_feedback_directional_gamma_integrable_of_theta_integrable
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (Q : TriadicCube 2) (hQ : Q ∈ descendantsAtDepth (originCube 2 m) 5)
    (e : Vec 2)
    (hThetaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        mixedOldTheta M m (Q) 0 ω)
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    Integrable (fun ω : Cutoff.CutoffSample 2 =>
      smoothFeedbackCellDirectionalGamma M m Q e ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hInt (i j : Fin 2) : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellGammaMatrix M m
          (Q) ω i j) μ := by
    have hMeas := smooth_feedback_gamma_matrix_entry_measurable M m Q i j
    refine hThetaInt.mono' hMeas.aestronglyMeasurable ?_
    filter_upwards with ω
    let N := smoothFeedbackCellGammaMatrix M m (Q) ω
    have hPSD : N.PosSemidef := by
      simpa [N] using smooth_feedback_cell_gamma_matrix_posSemidef
        M m (Q) ω
    have hSym : ∀ i j, N i j = N j i := by
      intro i j
      exact smooth_feedback_gamma_matrix_symmetric
        M m (Q) ω i j
    have hTraceEq : Matrix.trace N =
        smoothFeedbackCellDirectionalGammaTrace M m
          (Q) ω := by
      simpa [N] using smooth_feedback_gamma_matrix_trace_eq_directional_trace M m Q ω
    have hTraceNonneg : 0 ≤ Matrix.trace N := by
      rw [hTraceEq, smoothFeedbackCellDirectionalGammaTrace, Fin.sum_univ_two]
      exact add_nonneg
        (smooth_feedback_cell_directional_gamma_nonneg M m
          (Q) (basisVec 0) ω)
        (smooth_feedback_cell_directional_gamma_nonneg M m
          (Q) (basisVec 1) ω)
    calc
      ‖N i j‖ ≤ Matrix.trace N :=
        smooth_feedback_gamma_psd_entry_norm_le_trace hPSD hSym i j
      _ ≤ mixedOldTheta M m (Q) 0 ω := by
        calc
          Matrix.trace N = smoothFeedbackCellDirectionalGammaTrace M m
              (Q) ω := hTraceEq
          _ ≤ mixedOldTheta M m (Q) 0 ω :=
            smooth_feedback_directional_gamma_trace_le_local_old_theta
              M hγ m Q hQ ω
  have hGammaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        smoothFeedbackCellDirectionalGamma M m
          (Q) e ω) μ := by
    have hform (ω : Cutoff.CutoffSample 2) :
        smoothFeedbackCellDirectionalGamma M m
            (Q) e ω =
          ∑ i : Fin 2, ∑ j : Fin 2,
            e i * e j * smoothFeedbackCellGammaMatrix M m
              (Q) ω i j := by
      rw [← smooth_feedback_cell_gamma_matrix_quadratic_form]
      simp [vecDot, matVecMul, Fin.sum_univ_two]
      ring
    have hterm (i j : Fin 2) : Integrable
        (fun ω : Cutoff.CutoffSample 2 =>
          (e i * e j) * smoothFeedbackCellGammaMatrix M m
            (Q) ω i j) μ :=
      (hInt i j).const_mul (e i * e j)
    have hsum (i : Fin 2) : Integrable
        (fun ω : Cutoff.CutoffSample 2 => ∑ j : Fin 2,
          e i * e j * smoothFeedbackCellGammaMatrix M m
            (Q) ω i j) μ := by
      convert (hterm i 0).add (hterm i 1) using 1
      ext ω
      simp only [Fin.sum_univ_two]
      simp only [Pi.add_apply]
    have hsum2 : Integrable
        (fun ω : Cutoff.CutoffSample 2 => ∑ i : Fin 2, ∑ j : Fin 2,
          e i * e j * smoothFeedbackCellGammaMatrix M m
            (Q) ω i j) μ := by
      convert (hsum 0).add (hsum 1) using 1
      ext ω
      simp only [Fin.sum_univ_two]
      simp only [Pi.add_apply]
    exact hsum2.congr (Filter.Eventually.of_forall fun ω => (hform ω).symm)
  exact hGammaInt

/-- On every depth-five source cell, the directional Gamma is paid by the
accepted `mainEnvelopeXi` row. Integrability and the cap come from the
actual-law weighted row at `k=0`; the factor `1/2` is the planar half-trace. -/
theorem smooth_feedback_expected_directional_gamma_le_main_envelope_xi
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (Q : TriadicCube 2)
    (hQ : Q ∈ descendantsAtDepth (originCube 2 m) 5) (e : Vec 2) :
    (∫ ω, smoothFeedbackCellDirectionalGamma M m
      Q e ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (mainEnvelopeXi
        ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2)
        M.gamma mainSourceInversePrefix (theta M) 0 / 2) * vecNormSq e := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let xi := mainEnvelopeXi
    ((q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2)
    M.gamma mainSourceInversePrefix (theta M) 0
  have hrow := Main.main_envelope_xi_depth5_actual_law
    M h hM hγ N hpast m hm
  have hlocal := hrow 0 ⟨by norm_num, by norm_num⟩ Q hQ (0 : Fin 4)
  have hThetaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 => mixedOldTheta M m Q 0 ω) μ := by
    simpa [μ] using hlocal.1
  have hThetaCap :
      (∫ ω, mixedOldTheta M m Q 0 ω ∂μ) ≤ xi := by
    simpa [μ, xi] using hlocal.2
  calc
    (∫ ω, smoothFeedbackCellDirectionalGamma M m Q e ω ∂μ) ≤
        ((∫ ω, mixedOldTheta M m Q 0 ω ∂μ) / 2) * vecNormSq e :=
      smooth_feedback_expected_directional_gamma_le_half_local_old_theta
        M hγ m Q hQ e hThetaInt
    _ ≤ (xi / 2) * vecNormSq e :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hThetaCap
          (by norm_num : (0 : ℝ) ≤ 2))
        (vecNormSq_nonneg e)

end
end ASDExplicitGamma.Scalar
