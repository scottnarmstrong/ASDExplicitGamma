module

public import ASDExplicitGamma.Main.FrameMap
public import ASDExplicitGamma.Native.HeatIndividualComparison
public import ASDExplicitGamma.Native.GenericSourceBandEndpoint
public import ASDExplicitGamma.Native.OldSignedCompletedQ1
public import ASDExplicitGamma.Native.HeatInitialRefinedCoord
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Cold.NativeCellTrace

/-! The refined lag-minus-one child trace: sharp frame map, L20 bound `hp`, and mean `qstar`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped ENNReal
open ASDExplicitGamma.Gaussian

set_option linter.constructorNameAsVariable false

/-- The two block traces of an elliptic coarse response are strictly positive. -/
private theorem main_coarse_block_trace_pos {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    0 < Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft ∧
    0 < Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  let A := coarseBlockMatrix (cubeSet Q) a
  have hA : (toFullBlockMat A).PosDef := coarseBlockMatrix_posDef hnu hEll
  have hu0 : 0 < A.upperLeft 0 0 := by
    have h := hA.diag_pos (i := Sum.inl (0 : Fin 2))
    simpa [toFullBlockMat, A] using h
  have hu1 : 0 < A.upperLeft 1 1 := by
    have h := hA.diag_pos (i := Sum.inl (1 : Fin 2))
    simpa [toFullBlockMat, A] using h
  have hl0 : 0 < A.lowerRight 0 0 := by
    have h := hA.diag_pos (i := Sum.inr (0 : Fin 2))
    simpa [toFullBlockMat, A] using h
  have hl1 : 0 < A.lowerRight 1 1 := by
    have h := hA.diag_pos (i := Sum.inr (1 : Fin 2))
    simpa [toFullBlockMat, A] using h
  constructor
  · simpa [A, Matrix.trace, Fin.sum_univ_two] using add_pos hu0 hu1
  · simpa [A, Matrix.trace, Fin.sum_univ_two] using add_pos hl0 hl1

/-- Ellipticity and pointwise nonnegativity at a freely chosen positive frame
give the source trace-product bound. -/
private theorem main_coarse_block_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hpos := main_coarse_block_trace_pos hnu hEll
  let U := Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft
  let V := Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight
  let sigma : ℝ := 2 / V
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact div_pos (by norm_num) hpos.2
  have hdef := traceDefect_nonneg_of_ellipticFieldOn_triCube hnu hEll hsigma
  have hinv : sigma⁻¹ = V / 2 := by
    dsimp [sigma]
    field_simp [hpos.2.ne']
  have hscale : sigma * V = 2 := by
    dsimp [sigma]
    field_simp [hpos.2.ne']
    exact mul_inv_cancel₀ hpos.2.ne'
  change 0 ≤ sigma⁻¹ * U + sigma * V - 4 at hdef
  rw [hinv, hscale] at hdef
  dsimp [U, V] at hdef ⊢
  nlinarith


/-- The sharp scalar frame map: a trace defect read in a frame `rho >= 1` times larger. -/
theorem nativeHeatRefined_sharpFrameScalar {x y rho : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hprod : 4 ≤ x * y) (hrho : 1 ≤ rho) :
    x / rho + rho * y - 4 ≤
      (rho + rho⁻¹) / 2 * (x + y - 4) +
        (rho - rho⁻¹) / 2 * Real.sqrt ((x + y - 4) * (x + y - 4 + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
  have hrpos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hinv : rho⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hrho
  have hd : 0 ≤ (rho - rho⁻¹) / 2 := by linarith
  have hT : 0 ≤ x + y - 4 := by nlinarith [sq_nonneg (x - y)]
  have hsq : (y - x) ^ 2 ≤ (x + y - 4) * (x + y - 4 + 8) := by nlinarith
  have hsqrt : y - x ≤ Real.sqrt ((x + y - 4) * (x + y - 4 + 8)) :=
    Real.le_sqrt_of_sq_le hsq
  have hid : x / rho + rho * y - 4 =
      (rho + rho⁻¹) / 2 * (x + y - 4) + (rho - rho⁻¹) / 2 * (y - x) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
    field_simp
    ring
  rw [hid]
  have := mul_le_mul_of_nonneg_left hsqrt hd
  linarith

/-- Pathwise sharp frame map from the frame `m` to the frame `m+1` on the completed
cutoff `m+1`. -/
theorem nativeHeatRefined_sharpPathwise (M : ABKModel 2) (m n : ℤ)
    (omega : Cutoff.CutoffSample 2) :
    let rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ)
    let T0 : ℝ := traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu (m + 1) omega).toFun (Annealed.sigmaBar M m : ℝ)
    cutoffTraceDefect M (m + 1) n omega ≤
      (rho + rho⁻¹) / 2 * T0 + (rho - rho⁻¹) / 2 * Real.sqrt (T0 * (T0 + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
  dsimp only
  let A := coarseBlockMatrix (cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoff M.nu (m + 1) omega).toFun
  let sigmaK : ℝ := Annealed.sigmaBar M m
  let sigmaM : ℝ := Annealed.sigmaBar M (m + 1)
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  obtain ⟨Lambda, hEll⟩ := cutoff_isEllipticFieldOn_cube M (m + 1) omega (originCube 2 n)
  have htrpos := main_coarse_block_trace_pos M.nu_pos hEll
  have hsigmaK : 0 < sigmaK := (Annealed.sigmaBar_characterization M m).1
  have hratio : 1 ≤ rho := by
    have h := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).1
    simpa [rho, sigmaK, sigmaM] using h
  have hx : 0 < x := mul_pos (inv_pos.mpr hsigmaK) htrpos.1
  have hy : 0 < y := mul_pos hsigmaK htrpos.2
  have hprod : 4 ≤ x * y := by
    have hp := main_coarse_block_trace_product M.nu_pos hEll
    have hcancel : x * y = Matrix.trace A.upperLeft * Matrix.trace A.lowerRight := by
      dsimp [x, y]
      field_simp [hsigmaK.ne']
    rw [hcancel]
    exact hp
  have hsigmaM : sigmaM ≠ 0 := (Annealed.sigmaBar M (m + 1)).2.ne'
  have hxdiv : x / rho = sigmaM⁻¹ * Matrix.trace A.upperLeft := by
    dsimp [x, rho]
    field_simp [hsigmaK.ne', hsigmaM]
  have hydiv : rho * y = sigmaM * Matrix.trace A.lowerRight := by
    dsimp [rho, y]
    field_simp [hsigmaK.ne']
  have hnew : cutoffTraceDefect M (m + 1) n omega = x / rho + rho * y - 4 := by
    change sigmaM⁻¹ * Matrix.trace A.upperLeft +
      sigmaM * Matrix.trace A.lowerRight - 4 = _
    rw [← hxdiv, ← hydiv]
  have hold : traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu (m + 1) omega).toFun sigmaK = x + y - 4 := by
    dsimp [x, y, sigmaK, A]
    unfold traceDefect
    field_simp [hsigmaK.ne']
  rw [hnew, hold]
  exact nativeHeatRefined_sharpFrameScalar hx hy hprod hratio


/-- The `L²⁰` seminorm of `sqrt (T (T+8))` is at most `sqrt (t (t+8))` when `‖T‖₂₀ ≤ t`. -/
theorem nativeHeatRefined_eLpNorm'_sqrt_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → ℝ} (hT : Measurable T)
    (hT0 : ∀ ω, 0 ≤ T ω) {t : ℝ} (ht : 0 ≤ t) (hL : eLpNorm' T 20 μ ≤ ENNReal.ofReal t) :
    eLpNorm' (fun ω => Real.sqrt (T ω * (T ω + 8))) 20 μ ≤
      ENNReal.ofReal (Real.sqrt (t * (t + 8))) := by
  have hT8 : Measurable (fun ω => T ω + 8) := hT.add_const 8
  have hprod : eLpNorm' (fun ω => T ω * (T ω + 8)) 10 μ ≤
      eLpNorm' T 20 μ * eLpNorm' (fun ω => T ω + 8) 20 μ := by
    have h := eLpNorm'_smul_le_mul_eLpNorm' (μ := μ) (p := 10) (q := 20) (r := 20)
      (f := fun ω => T ω + 8) hT8.aestronglyMeasurable (φ := T) hT.aestronglyMeasurable
      (by norm_num) (by norm_num) (by norm_num)
    have hfun : (T • fun ω => T ω + 8) = fun ω => T ω * (T ω + 8) := by
      funext ω
      simp [smul_eq_mul]
    rw [hfun] at h
    exact h
  have h8 : eLpNorm' (fun ω => T ω + 8) 20 μ ≤ ENNReal.ofReal (t + 8) := by
    have hadd := eLpNorm'_add_le (μ := μ) (q := 20) hT.aestronglyMeasurable
      (g := fun _ => (8 : ℝ)) aestronglyMeasurable_const (by norm_num)
    have hc : eLpNorm' (fun _ : Ω => (8 : ℝ)) 20 μ = ENNReal.ofReal 8 := by
      rw [eLpNorm'_const _ (by norm_num : (0 : ℝ) < 20)]
      simp [Real.enorm_eq_ofReal]
    calc
      _ ≤ eLpNorm' T 20 μ + eLpNorm' (fun _ : Ω => (8 : ℝ)) 20 μ := hadd
      _ ≤ ENNReal.ofReal t + ENNReal.ofReal 8 := by rw [hc]; gcongr
      _ = ENNReal.ofReal (t + 8) := (ENNReal.ofReal_add ht (by norm_num)).symm
  have hprod' : eLpNorm' (fun ω => T ω * (T ω + 8)) 10 μ ≤
      ENNReal.ofReal (t * (t + 8)) := by
    calc
      _ ≤ eLpNorm' T 20 μ * eLpNorm' (fun ω => T ω + 8) 20 μ := hprod
      _ ≤ ENNReal.ofReal t * ENNReal.ofReal (t + 8) := by gcongr
      _ = _ := (ENNReal.ofReal_mul ht).symm
  have hsq : (fun ω => Real.sqrt (T ω * (T ω + 8))) =
      fun ω => ‖T ω * (T ω + 8)‖ ^ (1 / (2 : ℝ)) := by
    funext ω
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hT0 ω) (by linarith [hT0 ω]))]
  have hnorm : eLpNorm' (fun ω => Real.sqrt (T ω * (T ω + 8))) 20 μ =
      eLpNorm' (fun ω => T ω * (T ω + 8)) 10 μ ^ (1 / (2 : ℝ)) := by
    rw [hsq]
    have hh := eLpNorm'_norm_rpow (fun ω => T ω * (T ω + 8)) (20 : ℝ) (1 / (2 : ℝ))
      (by norm_num) (μ := μ)
    rw [hh]
    norm_num
  rw [hnorm]
  calc
    _ ≤ ENNReal.ofReal (t * (t + 8)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hprod' (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (t * (t + 8))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]


/-- Sharp `L²⁰` transfer along a pathwise affine-square-root frame map. -/
theorem nativeHeatRefined_eLpNorm'_frame_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T Tn : Ω → ℝ}
    (hT : Measurable T) (hTn : Measurable Tn)
    (hT0 : ∀ ω, 0 ≤ T ω) (hTn0 : ∀ ω, 0 ≤ Tn ω)
    {c d e t : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hpt : ∀ ω, Tn ω ≤ c * T ω + d * Real.sqrt (T ω * (T ω + 8)) + e)
    (hL : eLpNorm' T 20 μ ≤ ENNReal.ofReal t) :
    eLpNorm' Tn 20 μ ≤ ENNReal.ofReal (c * t + d * Real.sqrt (t * (t + 8)) + e) := by
  let S : Ω → ℝ := fun ω => Real.sqrt (T ω * (T ω + 8))
  have hS : Measurable S := by
    dsimp [S]
    exact Real.continuous_sqrt.measurable.comp (hT.mul (hT.add_const 8))
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Real.sqrt_nonneg _
  have hSL := nativeHeatRefined_eLpNorm'_sqrt_le hT hT0 ht hL
  let g : Ω → ℝ := fun ω => c * T ω + d * S ω + e
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => (hTn0 ω).trans (hpt ω)
  have hmono : eLpNorm' Tn 20 μ ≤ eLpNorm' g 20 μ := by
    apply eLpNorm'_mono_enorm_ae (by norm_num)
    filter_upwards [] with ω
    rw [Real.enorm_eq_ofReal (hTn0 ω), Real.enorm_eq_ofReal (hg0 ω)]
    exact ENNReal.ofReal_le_ofReal (hpt ω)
  have hcT : eLpNorm' (fun ω => c * T ω) 20 μ = ENNReal.ofReal c * eLpNorm' T 20 μ := by
    have := eLpNorm'_const_smul (μ := μ) (f := T) c (by norm_num : (0 : ℝ) < 20)
    simpa [Pi.smul_def, smul_eq_mul, Real.enorm_eq_ofReal hc] using this
  have hdS : eLpNorm' (fun ω => d * S ω) 20 μ = ENNReal.ofReal d * eLpNorm' S 20 μ := by
    have := eLpNorm'_const_smul (μ := μ) (f := S) d (by norm_num : (0 : ℝ) < 20)
    simpa [Pi.smul_def, smul_eq_mul, Real.enorm_eq_ofReal hd] using this
  have hconst : eLpNorm' (fun _ : Ω => e) 20 μ = ENNReal.ofReal e := by
    rw [eLpNorm'_const _ (by norm_num : (0 : ℝ) < 20)]
    simp [Real.enorm_eq_ofReal he]
  have h1 := eLpNorm'_add_le (μ := μ) (q := 20)
    ((hT.const_mul c).add (hS.const_mul d)).aestronglyMeasurable
    (g := fun _ => e) aestronglyMeasurable_const (by norm_num)
  have h2 := eLpNorm'_add_le (μ := μ) (q := 20)
    (hT.const_mul c).aestronglyMeasurable (g := fun ω => d * S ω)
    (hS.const_mul d).aestronglyMeasurable (by norm_num)
  calc
    eLpNorm' Tn 20 μ ≤ eLpNorm' g 20 μ := hmono
    _ ≤ eLpNorm' (fun ω => c * T ω + d * S ω) 20 μ + eLpNorm' (fun _ : Ω => e) 20 μ := h1
    _ ≤ (eLpNorm' (fun ω => c * T ω) 20 μ + eLpNorm' (fun ω => d * S ω) 20 μ) +
        eLpNorm' (fun _ : Ω => e) 20 μ := add_le_add h2 le_rfl
    _ = (ENNReal.ofReal c * eLpNorm' T 20 μ + ENNReal.ofReal d * eLpNorm' S 20 μ) +
        ENNReal.ofReal e := by rw [hcT, hdS, hconst]
    _ ≤ (ENNReal.ofReal c * ENNReal.ofReal t +
        ENNReal.ofReal d * ENNReal.ofReal (Real.sqrt (t * (t + 8)))) +
        ENNReal.ofReal e :=
      add_le_add (add_le_add (mul_le_mul_right hL _) (mul_le_mul_right hSL _)) le_rfl
    _ = ENNReal.ofReal (c * t + d * Real.sqrt (t * (t + 8)) + e) := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
        ← ENNReal.ofReal_add (mul_nonneg hc ht) (mul_nonneg hd (Real.sqrt_nonneg _)),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hc ht)
          (mul_nonneg hd (Real.sqrt_nonneg _))) he]


/-- The old-frame lag-minus-one trace at the completed cutoff `m+1`: `L²⁰` cap from the
gap-one individual cooperative system. -/
theorem nativeHeatRefined_oldFrame_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ j < m, nativeInductionState M h j)
    (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((nativeGap001Individual.1 : ℚ) : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let Φ := modelTraceObservable m M.nu (Annealed.sigmaBar M m)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives m M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
  have hΦ0 := modelTraceObservable_nonneg m M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
  let X : Cutoff.CutoffSample 2 → ℝ := fun ω => Φ (nativeSourceBandScalar m 1 1 ω)
  have hXeq (ω : Cutoff.CutoffSample 2) : X ω =
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ) := by
    have := native_source_band_trace_one M m 1 ω
    simpa [X, Φ] using this
  have hgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨C, hC, d, hd, _⟩ := hΦ.2
    exact ⟨C, hC, d, hd⟩
  have hmeasΦ : Measurable Φ := hΦ.1.continuous.measurable
  have hmem : MemLp X (ENNReal.ofReal 20) μ :=
    native_source_band_test_memLp M h hM m 1 le_rfl Φ hmeasΦ hgrowth 1 20 (by norm_num)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => hΦ0 _
  -- the moment curve at time one
  have hcomp := native_individual_cooperative_comparison M h hM hg m hpast hstate 0 1
    ⟨zero_le_one, le_rfl⟩ 20
  have hcurve : nativeIndividualMomentCurve M m 0 1 20 = ∫ ω, X ω ^ 20 ∂μ := by
    simp only [nativeIndividualMomentCurve, nativeSourceBandMomentK, nativeSourceBandAverage]
    have hgap : (nativeConfiguredSystem 0).gap = 1 := rfl
    rw [hgap]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [X, Φ, Real.rpow_natCast]
  have hz : (0 : ℝ) < ((nativeConfiguredSystem 0).system.z : ℝ) := by
    exact_mod_cast nativeConfiguredSystem_scale_pos 0
  have hmom : (∫ ω, X ω ^ 20 ∂μ) ≤
      (3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem 0).system.z : ℝ) ^ 20 *
        nativeVectorReal (nativeConfiguredSystem 0).result 20 := by
    have hn := hcomp
    simp only [nativeIndividualNormalizedMomentCurve, nativeConfiguredNormalizedMomentCurve,
      hcurve] at hn
    have h20 : (20 : Fin 21).val ≠ 0 := by decide
    simp only [h20, ite_false] at hn
    have hpos : 0 < (3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem 0).system.z : ℝ) ^ 20 := by
      positivity
    have := (div_le_iff₀ hpos).1 hn
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- from the moment to the L20 norm
  have hmemNat : MemLp X 20 μ := by simpa using hmem
  have hInt : Integrable (fun ω => ‖X ω‖ ^ 20) μ := hmemNat.integrable_norm_pow' (p := 20)
  have hint : Integrable (fun ω => X ω ^ 20) μ := by
    have heq : (fun ω => ‖X ω‖ ^ 20) = fun ω => X ω ^ 20 := by
      funext ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
    exact heq ▸ hInt
  have hlin : ∫⁻ ω, ‖X ω‖ₑ ^ (20 : ℝ) ∂μ = ENNReal.ofReal (∫ ω, X ω ^ 20 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hX0 ω) 20)]
    apply lintegral_congr
    intro ω
    rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      Real.enorm_eq_ofReal (hX0 ω), ENNReal.ofReal_pow (hX0 ω)]
  have hres : (0 : ℝ) ≤ nativeVectorReal (nativeConfiguredSystem 0).result 20 := by
    change (0 : ℝ) ≤ (((nativeGap001Result.getD 20 0 : ℚ)) : ℝ)
    norm_num [nativeGap001Result]
  have hroot : nativeRootValid (nativeGap001Result.getD 20 0) 20 = true := by
    decide +kernel
  have hsound := nativeRoot_sound hroot
  have hz' : (0 : ℝ) ≤ ((nativeConfiguredSystem 0).system.z : ℝ) := hz.le
  set A : ℝ := ∫ ω, X ω ^ 20 ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun ω => pow_nonneg (hX0 ω) 20
  have hrootA : A ^ ((20 : ℝ)⁻¹) ≤
      (3 / 50 : ℝ) * ((nativeConfiguredSystem 0).system.z : ℝ) *
        (nativeRootUp (nativeGap001Result.getD 20 0) 20 : ℝ) := by
    have hB := Real.rpow_le_rpow hA0 hmom (by norm_num : (0 : ℝ) ≤ (20 : ℝ)⁻¹)
    refine hB.trans ?_
    rw [Real.mul_rpow (by positivity) hres, Real.mul_rpow (by positivity) (by positivity)]
    have h1 : ((3 / 50 : ℝ) ^ 20) ^ ((20 : ℝ)⁻¹) = 3 / 50 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h2 : (((nativeConfiguredSystem 0).system.z : ℝ) ^ 20) ^ ((20 : ℝ)⁻¹) =
        ((nativeConfiguredSystem 0).system.z : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz']
      norm_num
    rw [h1, h2]
    have hres' : nativeVectorReal (nativeConfiguredSystem 0).result 20 =
        ((nativeGap001Result.getD 20 0 : ℚ) : ℝ) := rfl
    rw [hres']
    gcongr
    simpa using hsound
  have hind : (3 / 50 : ℝ) * ((nativeConfiguredSystem 0).system.z : ℝ) *
        (nativeRootUp (nativeGap001Result.getD 20 0) 20 : ℝ) ≤
      ((nativeGap001Individual.1 : ℚ) : ℝ) := by
    have hform := congrArg Prod.fst nativeGap001Individual_formula
    have hup := nativeUp_ge (nativeRootUp (nativeGap001Result.getD 20 0) 20 *
      nativeGap001Scale * nativeA)
    have hupR : ((nativeRootUp (nativeGap001Result.getD 20 0) 20 *
      nativeGap001Scale * nativeA : ℚ) : ℝ) ≤
        ((nativeGap001Individual.1 : ℚ) : ℝ) := by
      rw [← hform]
      exact_mod_cast hup
    have hz2 : ((nativeConfiguredSystem 0).system.z : ℝ) = (nativeGap001Scale : ℝ) := rfl
    rw [hz2]
    have hA2 : (nativeA : ℝ) = 3 / 50 := by norm_num [nativeA]
    calc
      _ = ((nativeRootUp (nativeGap001Result.getD 20 0) 20 *
          nativeGap001Scale * nativeA : ℚ) : ℝ) := by
        push_cast
        rw [hA2]
        ring
      _ ≤ _ := hupR
  have hfun : (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ)) = X := by
    funext ω
    exact (hXeq ω).symm
  rw [hfun]
  have hq20 : (0 : ℝ) < 20 := by norm_num
  calc
    eLpNorm' X 20 μ = (∫⁻ ω, ‖X ω‖ₑ ^ (20 : ℝ) ∂μ) ^ (1 / (20 : ℝ)) := rfl
    _ = (ENNReal.ofReal A) ^ (1 / (20 : ℝ)) := by rw [hlin]
    _ = ENNReal.ofReal (A ^ ((20 : ℝ)⁻¹)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num), one_div]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hrootA.trans hind)


/-- The one-label frame ratio is at most `1/(1-a)` with `a = (11/10)(2 γ₀)`. -/
theorem nativeHeatRefined_ratio_le (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    Real.rpow 3 (2 * M.gamma * ((1 : ℕ) : ℝ)) ≤
      1 / (1 - (((11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) : ℚ) : ℝ)) := by
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hg0 : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  set a : ℝ := (((11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) : ℚ) : ℝ) with ha
  have ha' : a = (11 / 10) * (2 * (17 / 50000 : ℝ)) := by
    rw [ha]; norm_num [nativeGamma]
  have ha1 : a < 1 := by rw [ha']; norm_num
  have hlog : Real.log 3 ≤ 11 / 10 := by
    have := Real.log_three_lt_d9
    norm_num at this ⊢
    linarith
  have hx : 2 * M.gamma * ((1 : ℕ) : ℝ) * Real.log 3 ≤ a := by
    rw [ha']
    have h1 : 2 * M.gamma * ((1 : ℕ) : ℝ) ≤ 2 * (17 / 50000 : ℝ) := by
      push_cast; linarith
    have h2 : 0 ≤ 2 * M.gamma * ((1 : ℕ) : ℝ) := by positivity
    calc
      _ ≤ (2 * (17 / 50000 : ℝ)) * (11 / 10) :=
        mul_le_mul h1 hlog (Real.log_nonneg (by norm_num)) (by norm_num)
      _ = _ := by ring
  have hexp : Real.rpow 3 (2 * M.gamma * ((1 : ℕ) : ℝ)) =
      Real.exp (2 * M.gamma * ((1 : ℕ) : ℝ) * Real.log 3) := by
    change (3 : ℝ) ^ (2 * M.gamma * ((1 : ℕ) : ℝ)) = _
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  rw [hexp]
  have hle : Real.exp (2 * M.gamma * ((1 : ℕ) : ℝ) * Real.log 3) ≤ Real.exp a :=
    Real.exp_le_exp.mpr hx
  have hden : 0 < 1 - a := by linarith
  have hkey : Real.exp a * (1 - a) ≤ 1 := by
    have h := Real.one_sub_le_exp_neg a
    have hpos := Real.exp_pos a
    have : Real.exp a * (1 - a) ≤ Real.exp a * Real.exp (-a) :=
      mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at this
    simpa using this
  refine hle.trans ?_
  rw [le_div_iff₀ hden]
  exact hkey

/-- Scalar monotonicity of the sharp frame coefficients. -/
theorem nativeHeatRefined_frameCoeff_mono {rho r : ℝ} (h1 : 1 ≤ rho) (hr : rho ≤ r) :
    (rho + rho⁻¹) / 2 ≤ (r + r⁻¹) / 2 ∧ (rho - rho⁻¹) / 2 ≤ (r - r⁻¹) / 2 := by
  have hrpos : 0 < rho := lt_of_lt_of_le zero_lt_one h1
  have hr1 : 0 < r := lt_of_lt_of_le hrpos hr
  have hinv : r⁻¹ ≤ rho⁻¹ := inv_anti₀ hrpos hr
  have hinv0 : rho⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  constructor
  · have : (r - rho) * (1 - (r * rho)⁻¹) ≥ 0 := by
      apply mul_nonneg (by linarith)
      have : (r * rho)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      linarith
    have e : (r + r⁻¹) - (rho + rho⁻¹) = (r - rho) * (1 - (r * rho)⁻¹) := by
      field_simp
      ring
    linarith
  · linarith


theorem nativeHeatRefined_oldFrameTrace_measurable (M : ABKModel 2) (m : ℤ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ)) := by
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives m M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
  have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable m M.nu (Annealed.sigmaBar M m) (nativeSourceBandScalar m 1 1 ω)) :=
    hΦ.1.continuous.measurable.comp (native_source_band_scalar_measurable m 1 1)
  convert hm using 1
  funext ω
  have := native_source_band_trace_one M m 1 ω
  simpa using this.symm

/-- The refined lag-minus-one child trace has the source `L²⁰` cap `hp`. -/
theorem nativeHeatRefined_childTrace_L20_le_hp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ j < m + 1, nativeInductionState M h j) :
    eLpNorm' (cutoffTraceDefect M (m + 1) m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((nativeHeatParametersData.hp : ℚ) : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hL := nativeHeatRefined_oldFrame_L20 M h hM hg m
    (fun j hj => hpast j (by omega)) (hpast m (by omega))
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ)
  have hT0 : ∀ ω, 0 ≤ T ω := by
    intro ω
    obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (m + 1) ω (originCube 2 m)
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M m).1
  set a : ℝ := (((11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) : ℚ) : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; norm_num [nativeGamma]
  have ha1 : a < 1 := by rw [ha]; norm_num [nativeGamma]
  set r : ℝ := 1 / (1 - a) with hr
  have hr1 : 1 ≤ r := by
    rw [hr]
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hrho := nativeHeatRefined_ratio_le M hg
  set c : ℝ := (r + r⁻¹) / 2
  set d : ℝ := (r - r⁻¹) / 2
  have hrpos : 0 < r := by linarith
  have hrinv0 : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hrinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hc0 : 0 ≤ c := by
    show 0 ≤ (r + r⁻¹) / 2
    linarith
  have hd0 : 0 ≤ d := by
    show 0 ≤ (r - r⁻¹) / 2
    linarith
  have hc1 : 1 ≤ c := by
    show 1 ≤ (r + r⁻¹) / 2
    have hmul : r * r⁻¹ = 1 := mul_inv_cancel₀ hrpos.ne'
    nlinarith [sq_nonneg (r - r⁻¹)]
  have hpt : ∀ ω, cutoffTraceDefect M (m + 1) m ω ≤
      c * T ω + d * Real.sqrt (T ω * (T ω + 8)) + 4 * (c - 1) := by
    intro ω
    have hp := nativeHeatRefined_sharpPathwise M m m ω
    dsimp only at hp
    set rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) with hrhodef
    have hrho1 : 1 ≤ rho := by
      have h1 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).1
      simpa [rho] using h1
    have hrhoR : rho ≤ r := by
      have h2 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).2
      have h2' : rho ≤ Real.rpow 3 (2 * M.gamma * ((1 : ℕ) : ℝ)) := by simpa [rho] using h2
      exact h2'.trans hrho
    obtain ⟨hmc0, hmd0⟩ := nativeHeatRefined_frameCoeff_mono hrho1 hrhoR
    have hmc : (rho + rho⁻¹) / 2 ≤ c := hmc0
    have hmd : (rho - rho⁻¹) / 2 ≤ d := hmd0
    have hT := hT0 ω
    have hsq : 0 ≤ Real.sqrt (T ω * (T ω + 8)) := Real.sqrt_nonneg _
    have e1 := mul_le_mul_of_nonneg_right hmc hT
    have e2 := mul_le_mul_of_nonneg_right hmd hsq
    have e3 : 4 * ((rho + rho⁻¹) / 2 - 1) ≤ 4 * (c - 1) := by linarith
    have hp' : cutoffTraceDefect M (m + 1) m ω ≤
        (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
          4 * ((rho + rho⁻¹) / 2 - 1) := hp
    linarith
  have hTm : Measurable T := nativeHeatRefined_oldFrameTrace_measurable M m
  have hTn : Measurable (cutoffTraceDefect M (m + 1) m) :=
    Variational.cutoffTraceDefect_measurable M (m + 1) m
  have hind0 : (0 : ℝ) ≤ ((nativeGap001Individual.1 : ℚ) : ℝ) := by
    norm_num [nativeGap001Individual]
  have hfinal := nativeHeatRefined_eLpNorm'_frame_le hTm hTn hT0
    (cutoffTraceDefect_nonneg M (m + 1) m) hc0 hd0 (by linarith) hind0 hpt hL
  refine hfinal.trans (ENNReal.ofReal_le_ofReal ?_)
  -- compare with the rational frame
  have hmin : min nativeGap001Old.x nativeGap001Individual.1 = nativeGap001Individual.1 := by
    apply min_eq_right
    decide +kernel
  have hvalid : nativeRootValid (nativeGap001Individual.1 * (nativeGap001Individual.1 + 8)) 2 = true := by
    decide +kernel
  have hd' : 0 ≤ (11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) ∧
      (11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) < 1 := by
    norm_num [nativeGamma]
  have hsound := nativeShiftedFrame_sound 1 nativeGap001Individual.1 hd' hvalid
  rw [nativeHeatHP_formula.symm, hmin]
  refine le_trans (le_of_eq ?_) hsound
  simp [nativeFrameReal, c, d, r, a, one_div]

end ASDExplicitGamma.Native
