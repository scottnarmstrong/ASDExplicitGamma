module

public import ASDExplicitGamma.Triadic.SensitivityODEUniformBound
public import ASDExplicitGamma.Triadic.SensitivityODEResponse
public import ASDExplicitGamma.Triadic.SensitivityODECalculus
public import ASDExplicitGamma.Triadic.SensitivityODEGauge
public import Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeRatio
public import Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.DescendantRatio

/-! Response ratios, aggregation, and continuity of the finite lambda history. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Homogenization.Book.Ch02 Homogenization.Book.Ch04
open Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

noncomputable section

/-- The root inverse-lambda along the affine coefficient path. -/
def sensitivityPathLambdaInverse {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q)) (u t : ℝ) : ℝ :=
  (Book.Ch02.lambdaSqFinite Q u 2
    (sensitivityPathFamily ν hν k kH t))⁻¹

theorem sensitivityDsharp_nonneg (Q : TriadicCube 2) (h : PlanarW2Infinity Q) :
    0 ≤ sensitivityDsharp Q h := by
  unfold sensitivityDsharp sensitivityD1 sensitivityD2
  have hK : 0 ≤ sensitivityKappaH := by
    unfold sensitivityKappaH planarC0 planarC1
    positivity
  exact add_nonneg
    (mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le
      (Real.sqrt_nonneg _)) (by
        unfold planarGradientLInf planarW1ValueLInf
        exact ENNReal.toReal_nonneg))
    (mul_nonneg hK
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (by
        unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
        exact ENNReal.toReal_nonneg)))

theorem sensitivityPathLambdaInverse_nonneg {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    {u : ℝ} (hu : 0 < u) (t : ℝ) :
    0 ≤ sensitivityPathLambdaInverse ν hν k kH u t := by
  unfold sensitivityPathLambdaInverse
  exact inv_nonneg.mpr (Book.Ch02.lambdaSq_finite_nonneg Q
    (sensitivityPathFamily ν hν k kH t) hu (by norm_num))

/-- A descendant response has a two-sided exponential ratio when the varying
lambda coefficient is bounded by a constant. -/
theorem sensitivity_descendant_responseJ_twoSided_exp_const
    {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2)
    {u K : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4) (_hK : 0 ≤ K)
    (hcoeff : ∀ τ, sensitivityB2 * sensitivityDsharp Q h *
        sensitivityPathLambdaInverse ν hν k kH u τ ≤ K)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    let y := fun τ => responseJ (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q
    y t₂ ≤ Real.exp (K * (t₂ - t₁)) * y t₁ ∧
      y t₁ ≤ Real.exp (K * (t₂ - t₁)) * y t₂ := by
  dsimp
  let y := fun τ => responseJ (Book.Ch02.cubeDomain R)
    (sensitivityBookCoeffOn R ν hν
      (sensitivityResponseCoefficientPath
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q
  have hy (τ : ℝ) : 0 ≤ y τ :=
    Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q
  have hderiv (τ : ℝ) : HasDerivAt y (deriv y τ) τ := by
    have hpath := sensitivity_descendant_responseJ_hasDerivAt
      ν hν k kH h hkH hR q τ
    have heq : deriv y τ = (1 / 2 : ℝ) * blockVecDot (0, -q)
        (blockMatVecMul
          (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
            (Book.Ch02.cubeDomain R)
            (sensitivityBookCoeffOn R ν hν
              (sensitivityResponseCoefficientPath
                (sensitivityResponseCoefficientRestrict k hR)
                (sensitivityResponseCoefficientRestrict kH hR) τ))
            (sensitivitySkewMatrixDirection (h.restrict hR)).1) (0, -q)) := by
      simpa [y] using hpath.deriv
    rw [heq]
    exact hpath
  have habs (τ : ℝ) : |deriv y τ| ≤ K * y τ := by
    have hraw := sensitivity_descendant_responseJ_deriv_abs_le
      ν hν k kH h hkH hR q u hu hu4 τ
    have hcompare := mul_le_mul_of_nonneg_right (hcoeff τ) (hy τ)
    simpa [y, sensitivityPathLambdaInverse, mul_assoc] using hraw.trans hcompare
  have hupper (τ : ℝ) : deriv y τ ≤ K * y τ := (abs_le.mp (habs τ)).2
  have hlower (τ : ℝ) : -(K * y τ) ≤ deriv y τ := by
    have h := (abs_le.mp (habs τ)).1
    linarith
  have hup := sensitivity_exp_integral_of_hasDerivAt_le hderiv
    continuous_const (fun τ _ _ => by simpa using hupper τ) ht
  have hdown := sensitivity_le_exp_integral_mul_of_neg_hasDerivAt_le hderiv
    continuous_const (fun τ _ _ => by simpa using hlower τ) ht
  constructor
  · simpa [intervalIntegral.integral_const, y, mul_comm] using hup
  · simpa [intervalIntegral.integral_const, y, mul_comm] using hdown

/-- A response ratio on every descendant transfers to the finite multiscale
inverse-lambda history. -/
theorem sensitivityPathLambdaInverse_ratio_of_descendant_responseJ
    {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q)) {u ρ t₁ t₂ : ℝ}
    (hu : 0 < u) (hρ : 0 ≤ ρ)
    (hJ : ∀ (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j), ∀ q : Vec 2,
        responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₂)) 0 q ≤
        ρ * responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₁)) 0 q) :
    sensitivityPathLambdaInverse ν hν k kH u t₂ ≤
      ρ * sensitivityPathLambdaInverse ν hν k kH u t₁ := by
  let F₀ := sensitivityPathFamily ν hν k kH t₁
  let F₁ := sensitivityPathFamily ν hν k kH t₂
  have hdesc : ∀ (kscale : ℤ), kscale ≤ Q.scale →
      ∀ R ∈ descendantsAtScale Q kscale,
        coarseSigmaStarInvMatrixNorm R F₁ ≤
          ρ * coarseSigmaStarInvMatrixNorm R F₀ := by
    intro kscale hkScale R hRscale
    let j : ℕ := Int.toNat (Q.scale - kscale)
    have hRdepth : R ∈ descendantsAtDepth Q j := by
      have hh := hRscale
      rw [descendantsAtScale_eq_descendantsAtDepth Q hkScale] at hh
      simpa [j] using hh
    let kR := sensitivityResponseCoefficientRestrict k hRdepth
    let kHR := sensitivityResponseCoefficientRestrict kH hRdepth
    have hae₁ := sensitivityPathFamily_descendant_coeffOn_aeeq
      ν hν k kH hRdepth t₁
    have hae₂ := sensitivityPathFamily_descendant_coeffOn_aeeq
      ν hν k kH hRdepth t₂
    rw [coarseSigmaStarInvMatrixNorm, coarseSigmaStarInvMatrixNorm,
      Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hae₂,
      Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hae₁]
    exact Algsuperdiff.Section24.Sensitivity.Provider.Lambda.matrixNorm_sigmaStarInvCoarse_le_of_responseJ_le
        (Book.Ch02.cubeDomain R)
        (sensitivityBookCoeffOn R ν hν
          (sensitivityResponseCoefficientPath kR kHR t₁))
        (sensitivityBookCoeffOn R ν hν
          (sensitivityResponseCoefficientPath kR kHR t₂)) hρ
        (hJ j R hRdepth)
  have hagg := lambdaSqFinite_inv_le_of_descendant_ratio Q F₀ F₁
    hρ hu (by norm_num : (1 : ℝ) ≤ 2) hdesc
  simpa [sensitivityPathLambdaInverse, F₀, F₁, Book.Ch02.lambdaSqFinite] using hagg

/-- Two-sided exponential control of the aggregate, using the uniform
ellipticity bound only to obtain a constant Gronwall coefficient. -/
theorem sensitivityPathLambdaInverse_twoSided_exp_const {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    sensitivityPathLambdaInverse ν hν k kH u t₂ ≤
      Real.exp ((sensitivityB2 * sensitivityDsharp Q h * (8 * ν⁻¹)) *
        (t₂ - t₁)) * sensitivityPathLambdaInverse ν hν k kH u t₁ ∧
    sensitivityPathLambdaInverse ν hν k kH u t₁ ≤
      Real.exp ((sensitivityB2 * sensitivityDsharp Q h * (8 * ν⁻¹)) *
        (t₂ - t₁)) * sensitivityPathLambdaInverse ν hν k kH u t₂ := by
  let M := 8 * ν⁻¹
  let K := sensitivityB2 * sensitivityDsharp Q h * M
  have hB : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
  have hD : 0 ≤ sensitivityDsharp Q h := sensitivityDsharp_nonneg Q h
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcoeff (τ : ℝ) : sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u τ ≤ K := by
    have hL := sensitivityPath_lambdaSqFinite_inv_le_uniform ν hν k kH hu τ
    dsimp [K, M]
    exact mul_le_mul_of_nonneg_left hL (mul_nonneg hB hD)
  have hJup (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2) :
      responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₂)) 0 q ≤
        Real.exp (K * (t₂ - t₁)) * responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₁)) 0 q :=
    (sensitivity_descendant_responseJ_twoSided_exp_const ν hν k kH h hkH
      hR q hu hu4 hK hcoeff ht).1
  have hJdown (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2) :
      responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₁)) 0 q ≤
        Real.exp (K * (t₂ - t₁)) * responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₂)) 0 q :=
    (sensitivity_descendant_responseJ_twoSided_exp_const ν hν k kH h hkH
      hR q hu hu4 hK hcoeff ht).2
  have hρ : 0 ≤ Real.exp (K * (t₂ - t₁)) := (Real.exp_pos _).le
  have hup := sensitivityPathLambdaInverse_ratio_of_descendant_responseJ
    ν hν k kH hu hρ hJup
  have hdown := sensitivityPathLambdaInverse_ratio_of_descendant_responseJ
    ν hν k kH hu hρ hJdown
  constructor
  · simpa [K, M, mul_assoc, mul_comm, mul_left_comm] using hup
  · simpa [K, M, mul_assoc, mul_comm, mul_left_comm] using hdown

/-- The inverse-lambda history is continuous in the affine path parameter. -/
theorem sensitivityPathLambdaInverse_continuous {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4) :
    Continuous (sensitivityPathLambdaInverse ν hν k kH u) := by
  apply Metric.continuous_iff.mpr
  intro s ε hε
  let M : ℝ := 8 * ν⁻¹
  let K : ℝ := sensitivityB2 * sensitivityDsharp Q h * M
  have hB : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
  have hD : 0 ≤ sensitivityDsharp Q h := sensitivityDsharp_nonneg Q h
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL (t : ℝ) :
      sensitivityPathLambdaInverse ν hν k kH u t ≤ M := by
    exact sensitivityPath_lambdaSqFinite_inv_le_uniform ν hν k kH hu t
  have hL0 (t : ℝ) :
      0 ≤ sensitivityPathLambdaInverse ν hν k kH u t :=
    sensitivityPathLambdaInverse_nonneg ν hν k kH hu t
  have hg : Continuous (fun t : ℝ =>
      M * (Real.exp (K * |t - s|) - 1)) := by
    have harg : Continuous (fun t : ℝ => K * |t - s|) :=
      continuous_const.mul ((continuous_id.sub continuous_const).abs)
    have hsub : Continuous (fun t : ℝ => Real.exp (K * |t - s|) - 1) :=
      (Real.continuous_exp.comp harg).sub continuous_const
    exact continuous_const.mul hsub
  have hgAt := hg.continuousAt (x := s)
  have hgzero : M * (Real.exp (K * |s - s|) - 1) = 0 := by simp
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hgAt ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hdiff : |sensitivityPathLambdaInverse ν hν k kH u t -
      sensitivityPathLambdaInverse ν hν k kH u s| ≤
        M * (Real.exp (K * |t - s|) - 1) := by
    rcases le_total s t with hst | hts
    · have hratio := sensitivityPathLambdaInverse_twoSided_exp_const
        ν hν k kH h hkH hu hu4 hst
      have hE : 1 ≤ Real.exp (K * (t - s)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hK (sub_nonneg.mpr hst))
      have hdist : |t - s| = t - s := abs_of_nonneg (sub_nonneg.mpr hst)
      rw [hdist]
      apply abs_le.mpr
      constructor
      · have hlow := hratio.2
        calc
          -(M * (Real.exp (K * (t - s)) - 1)) ≤
              -(sensitivityPathLambdaInverse ν hν k kH u s -
                sensitivityPathLambdaInverse ν hν k kH u t) := by
                  have hupper := calc
                    sensitivityPathLambdaInverse ν hν k kH u s -
                        sensitivityPathLambdaInverse ν hν k kH u t ≤
                        (Real.exp (K * (t - s)) - 1) *
                          sensitivityPathLambdaInverse ν hν k kH u t := by nlinarith [hlow]
                    _ ≤ (Real.exp (K * (t - s)) - 1) * M :=
                      mul_le_mul_of_nonneg_left (hL t) (by linarith)
                  nlinarith [hupper]
          _ = sensitivityPathLambdaInverse ν hν k kH u t -
              sensitivityPathLambdaInverse ν hν k kH u s := by ring
      · have hup := hratio.1
        have hupper := calc
          sensitivityPathLambdaInverse ν hν k kH u t -
              sensitivityPathLambdaInverse ν hν k kH u s ≤
              (Real.exp (K * (t - s)) - 1) *
                sensitivityPathLambdaInverse ν hν k kH u s := by nlinarith [hup]
          _ ≤ (Real.exp (K * (t - s)) - 1) * M :=
            mul_le_mul_of_nonneg_left (hL s) (by linarith)
        nlinarith [hupper]
    · have hratio := sensitivityPathLambdaInverse_twoSided_exp_const
        ν hν k kH h hkH hu hu4 hts
      have hE : 1 ≤ Real.exp (K * (s - t)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hK (sub_nonneg.mpr hts))
      have hdist : |t - s| = s - t := by
        rw [abs_of_nonpos (sub_nonpos.mpr hts)]
        ring
      rw [hdist]
      apply abs_le.mpr
      constructor
      · have hup := hratio.1
        have hupper := calc
          sensitivityPathLambdaInverse ν hν k kH u s -
              sensitivityPathLambdaInverse ν hν k kH u t ≤
              (Real.exp (K * (s - t)) - 1) *
                sensitivityPathLambdaInverse ν hν k kH u t := by nlinarith [hup]
          _ ≤ (Real.exp (K * (s - t)) - 1) * M :=
            mul_le_mul_of_nonneg_left (hL t) (by linarith)
        nlinarith [hupper]
      · have hlow := hratio.2
        have hupper := calc
          sensitivityPathLambdaInverse ν hν k kH u t -
              sensitivityPathLambdaInverse ν hν k kH u s ≤
              (Real.exp (K * (s - t)) - 1) *
                sensitivityPathLambdaInverse ν hν k kH u s := by nlinarith [hlow]
          _ ≤ (Real.exp (K * (s - t)) - 1) * M :=
            mul_le_mul_of_nonneg_left (hL s) (by linarith)
        nlinarith [hupper]
  have hnear' := hnear (x := t) ht
  have hgt : M * (Real.exp (K * |t - s|) - 1) < ε := by
    rw [dist_eq_norm, Real.norm_eq_abs, hgzero, sub_zero] at hnear'
    have hnonneg : 0 ≤ M * (Real.exp (K * |t - s|) - 1) := by
      apply mul_nonneg hM
      have : 0 ≤ K * |t - s| := mul_nonneg hK (abs_nonneg _)
      linarith [Real.one_le_exp_iff.mpr this]
    have := (abs_lt.mp hnear')
    linarith
  have hdistL := hdiff
  rw [dist_eq_norm, Real.norm_eq_abs]
  exact lt_of_le_of_lt hdistL hgt

/-- The sharp descendant response ratio with the actual variable lambda
coefficient. -/
theorem sensitivity_descendant_responseJ_exp_integral
    {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (hLcont : Continuous (sensitivityPathLambdaInverse ν hν k kH u))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    let c := fun τ => sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u τ
    let y := fun τ => responseJ (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q
    y t₂ ≤ Real.exp (∫ τ in t₁..t₂, c τ) * y t₁ := by
  dsimp
  let c := fun τ => sensitivityB2 * sensitivityDsharp Q h *
    sensitivityPathLambdaInverse ν hν k kH u τ
  let y := fun τ => responseJ (Book.Ch02.cubeDomain R)
    (sensitivityBookCoeffOn R ν hν
      (sensitivityResponseCoefficientPath
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q
  have hc : Continuous c := by
    dsimp [c]
    have hc₀ : Continuous (fun _ : ℝ =>
        sensitivityB2 * sensitivityDsharp Q h) := continuous_const
    exact hc₀.mul hLcont
  have hy (τ : ℝ) : 0 ≤ y τ :=
    Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q
  have hpath (τ : ℝ) := sensitivity_descendant_responseJ_hasDerivAt
    ν hν k kH h hkH hR q τ
  have hderiv (τ : ℝ) : HasDerivAt y (deriv y τ) τ := by
    have heq : deriv y τ = (1 / 2 : ℝ) * blockVecDot (0, -q)
        (blockMatVecMul
          (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
            (Book.Ch02.cubeDomain R)
            (sensitivityBookCoeffOn R ν hν
              (sensitivityResponseCoefficientPath
                (sensitivityResponseCoefficientRestrict k hR)
                (sensitivityResponseCoefficientRestrict kH hR) τ))
            (sensitivitySkewMatrixDirection (h.restrict hR)).1) (0, -q)) := by
      simpa [y] using (hpath τ).deriv
    rw [heq]
    exact hpath τ
  have hbound (τ : ℝ) : deriv y τ ≤ c τ * y τ := by
    have hraw := sensitivity_descendant_responseJ_deriv_abs_le
      ν hν k kH h hkH hR q u hu hu4 τ
    have hle := (abs_le.mp hraw).2
    simpa [c, y, sensitivityPathLambdaInverse, mul_assoc] using hle
  have hgron := sensitivity_exp_integral_of_hasDerivAt_le hderiv hc
    (fun τ _ _ => hbound τ) ht
  simpa [c, y] using hgron

/-- The variable-coefficient response ratio transfers to the finite
multiscale inverse-lambda history. -/
theorem sensitivityPathLambdaInverse_ratio_variable
    {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (hLcont : Continuous (sensitivityPathLambdaInverse ν hν k kH u))
    {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    sensitivityPathLambdaInverse ν hν k kH u t₂ ≤
      Real.exp (∫ τ in t₁..t₂,
        sensitivityB2 * sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u τ) *
        sensitivityPathLambdaInverse ν hν k kH u t₁ := by
  let c := fun τ => sensitivityB2 * sensitivityDsharp Q h *
    sensitivityPathLambdaInverse ν hν k kH u τ
  have hJ (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2) :
      responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₂)) 0 q ≤
        Real.exp (∫ τ in t₁..t₂, c τ) * responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t₁)) 0 q := by
    have h := sensitivity_descendant_responseJ_exp_integral
      ν hν k kH h hkH hR q hu hu4 hLcont ht
    simpa [c] using h
  have hρ : 0 ≤ Real.exp (∫ τ in t₁..t₂, c τ) :=
    (Real.exp_pos _).le
  have hagg := sensitivityPathLambdaInverse_ratio_of_descendant_responseJ
    ν hν k kH hu hρ hJ
  simpa [c] using hagg

/-- A constant skew shift of the direction leaves every descendant reciprocal
block, and therefore the full finite inverse-lambda history, unchanged. -/
theorem sensitivityPathLambdaInverse_constant_direction_shift
    {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q)) (g : ℝ)
    {u t : ℝ} :
    sensitivityPathLambdaInverse ν hν k
        (kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) u t =
      sensitivityPathLambdaInverse ν hν k kH u t := by
  let F₁ := sensitivityPathFamily ν hν k
    (kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) t
  let F₀ := sensitivityPathFamily ν hν k kH t
  have hnorm (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) :
      Book.Ch02.coarseSigmaStarInvMatrixNorm R F₁ =
        Book.Ch02.coarseSigmaStarInvMatrixNorm R F₀ := by
    let kR := sensitivityResponseCoefficientRestrict k hR
    let kHR := sensitivityResponseCoefficientRestrict kH hR
    let kHRplus := sensitivityResponseCoefficientRestrict
      (kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) hR
    have hrestrict := sensitivityResponseCoefficientRestrict_add_const kH hR g
    have hlocal : sensitivityResponseCoefficientPath kR kHRplus t =
        sensitivityResponseCoefficientPath kR kHR t +
          BoundedContinuousFunction.const (closure (openCubeSet R)) (t * g) := by
      rw [show kHRplus = kHR + BoundedContinuousFunction.const (closure (openCubeSet R)) g
        from hrestrict]
      exact sensitivityResponseCoefficientPath_add_const kR kHR g t
    have hcoeff₁ := sensitivityPathFamily_descendant_coeffOn_aeeq
      ν hν k (kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) hR t
    have hcoeff₀ := sensitivityPathFamily_descendant_coeffOn_aeeq
      ν hν k kH hR t
    unfold Book.Ch02.coarseSigmaStarInvMatrixNorm
    rw [Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hcoeff₁,
      Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq hcoeff₀]
    apply congrArg (fun A : Mat 2 => matrixNorm A)
    rw [hlocal]
    exact sensitivityBookCoeffOn_constantShift_sigmaStarInv R ν hν
      (sensitivityResponseCoefficientPath kR kHR t) (t * g)
  have hmax (j : ℕ) :
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (j : ℤ)) F₁ =
        Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (j : ℤ)) F₀ := by
    unfold Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    have hk : Q.scale - (j : ℤ) ≤ Q.scale := by omega
    have hdepth : R ∈ descendantsAtDepth Q j := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
      simpa using hR
    exact hnorm j R hdepth
  have hsum :
      (∑' j : ℕ, Book.Ch02.geometricWeight u 2 j *
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (j : ℤ)) F₁) (1 : ℝ)) =
      (∑' j : ℕ, Book.Ch02.geometricWeight u 2 j *
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (j : ℤ)) F₀) (1 : ℝ)) := by
    apply tsum_congr
    intro j
    rw [hmax j]
  have hLamEq : Book.Ch02.lambdaSqFinite Q u 2 F₁ =
      Book.Ch02.lambdaSqFinite Q u 2 F₀ := by
    unfold Book.Ch02.lambdaSqFinite
    simp only [show (2 : ℝ) / 2 = 1 by norm_num]
    exact congrArg (fun z : ℝ => Real.rpow z (-1 : ℝ)) hsum
  unfold sensitivityPathLambdaInverse
  exact congrArg (fun z : ℝ => z⁻¹) hLamEq

/-- The scalar inverse-lambda component of the coarse sensitivity ODE. -/
theorem sensitivityPathLambdaInverse_rational_envelope {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (hsmall : sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u 0 < 1) :
    sensitivityPathLambdaInverse ν hν k kH u 1 ≤
      sensitivityPathLambdaInverse ν hν k kH u 0 /
        (1 - sensitivityB2 * sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0) := by
  let f := sensitivityPathLambdaInverse ν hν k kH u
  let C := sensitivityB2 * sensitivityDsharp Q h
  have hfcont : Continuous f := by
    exact sensitivityPathLambdaInverse_continuous ν hν k kH h hkH hu hu4
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by unfold sensitivityB2; positivity)
      (sensitivityDsharp_nonneg Q h)
  have hfnonneg : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f t := by
    intro t _ _
    exact sensitivityPathLambdaInverse_nonneg ν hν k kH hu t
  have hratio : ∀ t, 0 ≤ t → t ≤ 1 →
      f t ≤ Real.exp (∫ τ in (0:ℝ)..t, C * f τ) * f 0 := by
    intro t ht0 ht1
    have h := sensitivityPathLambdaInverse_ratio_variable ν hν k kH h hkH
      hu hu4 hfcont (t₁ := 0) (t₂ := t) ht0
    simpa [f, C] using h
  have hsmall' : C * f 0 < 1 := by simpa [f, C] using hsmall
  have hmain := sensitivity_bihari_upper_envelope hfcont hC hfnonneg hratio hsmall'
  simpa [f, C] using hmain

end

end ASDExplicitGamma.Triadic
