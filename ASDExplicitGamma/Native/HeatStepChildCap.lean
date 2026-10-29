module

public import ASDExplicitGamma.Native.HeatInitialRefinedFrame
public import ASDExplicitGamma.Native.HeatActualOldProfile
public import ASDExplicitGamma.Native.GenericSourceChildBandEndpoint
public import ASDExplicitGamma.Native.GenericSourceChildBandFactors
public import ASDExplicitGamma.Native.HeatStepIndivNum
public import ASDExplicitGamma.Native.HeatStepFrameNum

/-! The origin child trace in the old frame `σ̄_m` at the completed cutoff `m+1+ns`,
from the gap `ns+1` individual cooperative system and the OLD row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped ENNReal
open ASDExplicitGamma.Gaussian

/-- The physical trace of the refined child `i`. -/
noncomputable def nativeHeatStepChildTraceCC (M : ABKModel 2) (m : ℤ) (ns : ℕ)
    (i : nativeHeatQ3RefinedCarrierIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  traceDefect (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
    (Annealed.sigmaBar M (m + 1) : ℝ)

/-- Route (a): the individual cooperative system. -/
theorem nativeHeatStep_originChild_individual (ns : ℕ) (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hind : NativeHeatStepIndivNum ns hns160) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun (Annealed.sigmaBar M m : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((nativeHeatIndividualGen ns).1 : ℚ) : ℝ) := by
  classical
  let idx := nativeHeatIndexGen ns hns160
  let g := (nativeConfiguredSystem idx).gap
  have hgap : g = ns + 1 := hind.gap
  have hg1 : 1 ≤ g := by omega
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let Φ := modelTraceObservable m M.nu (Annealed.sigmaBar M m)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives m M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
  have hΦ0 := modelTraceObservable_nonneg m M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
  let X : Cutoff.CutoffSample 2 → ℝ := fun ω => Φ (nativeSourceBandScalar m g 1 ω)
  have hXeq (ω : Cutoff.CutoffSample 2) : X ω =
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M m : ℝ) := by
    have := native_source_band_trace_one M m g ω
    have hc : m + (g : ℤ) = m + 1 + (ns : ℤ) := by rw [hgap]; push_cast; ring
    rw [hc] at this
    simpa [X, Φ] using this
  have hgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨C, hC, d, hd, _⟩ := hΦ.2
    exact ⟨C, hC, d, hd⟩
  have hmeasΦ : Measurable Φ := hΦ.1.continuous.measurable
  have hmem : MemLp X (ENNReal.ofReal 20) μ :=
    native_source_band_test_memLp M h hM m g hg1 Φ hmeasΦ hgrowth 1 20 (by norm_num)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => hΦ0 _
  have hcomp := native_individual_cooperative_comparison M h hM hg m hpast hstate idx 1
    ⟨zero_le_one, le_rfl⟩ 20
  have hcurve : nativeIndividualMomentCurve M m idx 1 20 = ∫ ω, X ω ^ 20 ∂μ := by
    simp only [nativeIndividualMomentCurve, nativeSourceBandMomentK, nativeSourceBandAverage]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [X, Φ, g, Real.rpow_natCast]
  have hz : (0 : ℝ) < ((nativeConfiguredSystem idx).system.z : ℝ) := by
    exact_mod_cast nativeConfiguredSystem_scale_pos idx
  have hmom : (∫ ω, X ω ^ 20 ∂μ) ≤
      (3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem idx).system.z : ℝ) ^ 20 *
        nativeVectorReal (nativeConfiguredSystem idx).result 20 := by
    have hn := hcomp
    simp only [nativeIndividualNormalizedMomentCurve, nativeConfiguredNormalizedMomentCurve,
      hcurve] at hn
    have h20 : (20 : Fin 21).val ≠ 0 := by decide
    simp only [h20, ite_false] at hn
    have hpos : 0 < (3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem idx).system.z : ℝ) ^ 20 := by
      positivity
    have := (div_le_iff₀ hpos).1 hn
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
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
  have hroot := hind.result20_root
  have hs := of_decide_eq_true hroot
  have hres : (0 : ℝ) ≤ nativeVectorReal (nativeConfiguredSystem idx).result 20 := by
    have : (0 : ℚ) ≤ (nativeConfiguredSystem idx).result.getD 20 0 := hs.2.1
    change (0 : ℝ) ≤ (((nativeConfiguredSystem idx).result.getD 20 0 : ℚ) : ℝ)
    exact_mod_cast this
  have hsound := nativeRoot_sound hroot
  have hz' : (0 : ℝ) ≤ ((nativeConfiguredSystem idx).system.z : ℝ) := hz.le
  set A : ℝ := ∫ ω, X ω ^ 20 ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun ω => pow_nonneg (hX0 ω) 20
  have hrootA : A ^ ((20 : ℝ)⁻¹) ≤
      (3 / 50 : ℝ) * ((nativeConfiguredSystem idx).system.z : ℝ) *
        (nativeRootUp ((nativeConfiguredSystem idx).result.getD 20 0) 20 : ℝ) := by
    have hB := Real.rpow_le_rpow hA0 hmom (by norm_num : (0 : ℝ) ≤ (20 : ℝ)⁻¹)
    refine hB.trans ?_
    rw [Real.mul_rpow (by positivity) hres, Real.mul_rpow (by positivity) (by positivity)]
    have h1 : ((3 / 50 : ℝ) ^ 20) ^ ((20 : ℝ)⁻¹) = 3 / 50 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h2 : (((nativeConfiguredSystem idx).system.z : ℝ) ^ 20) ^ ((20 : ℝ)⁻¹) =
        ((nativeConfiguredSystem idx).system.z : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz']
      norm_num
    rw [h1, h2]
    have hres' : nativeVectorReal (nativeConfiguredSystem idx).result 20 =
        (((nativeConfiguredSystem idx).result.getD 20 0 : ℚ) : ℝ) := rfl
    rw [hres']
    gcongr
    simpa using hsound
  have hind' : (3 / 50 : ℝ) * ((nativeConfiguredSystem idx).system.z : ℝ) *
        (nativeRootUp ((nativeConfiguredSystem idx).result.getD 20 0) 20 : ℝ) ≤
      (((nativeHeatIndividualGen ns).1 : ℚ) : ℝ) := by
    have hform := congrArg Prod.fst hind.indiv
    have hup := nativeUp_ge (nativeRootUp ((nativeConfiguredSystem idx).result.getD 20 0) 20 *
      (nativeConfiguredSystem idx).system.z * nativeA)
    have hupR : ((nativeRootUp ((nativeConfiguredSystem idx).result.getD 20 0) 20 *
      (nativeConfiguredSystem idx).system.z * nativeA : ℚ) : ℝ) ≤
        (((nativeHeatIndividualGen ns).1 : ℚ) : ℝ) := by
      rw [hform]
      exact_mod_cast hup
    have hA2 : (nativeA : ℝ) = 3 / 50 := by norm_num [nativeA]
    calc
      _ = ((nativeRootUp ((nativeConfiguredSystem idx).result.getD 20 0) 20 *
          (nativeConfiguredSystem idx).system.z * nativeA : ℚ) : ℝ) := by
        push_cast
        rw [hA2]
        ring
      _ ≤ _ := hupR
  have hfun : (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M m : ℝ)) = X := by
    funext ω
    exact (hXeq ω).symm
  rw [hfun]
  calc
    eLpNorm' X 20 μ = (∫⁻ ω, ‖X ω‖ₑ ^ (20 : ℝ) ∂μ) ^ (1 / (20 : ℝ)) := rfl
    _ = (ENNReal.ofReal A) ^ (1 / (20 : ℝ)) := by rw [hlin]
    _ = ENNReal.ofReal (A ^ ((20 : ℝ)⁻¹)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num), one_div]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hrootA.trans hind')

/-- Route (b): the OLD row. -/
theorem nativeHeatStep_originChild_oldRow (ns : ℕ) (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hind : NativeHeatStepIndivNum ns hns160) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun (Annealed.sigmaBar M m : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((nativeHeatOldRowGen ns).x : ℚ) : ℝ) := by
  have hcap := native_source_band_L20_le_configured_old M h hM hg m hpast hstate
    (nativeHeatIndexGen ns hns160)
  rw [hind.gap, hind.old_source] at hcap
  have h1 := hcap 1 ⟨zero_le_one, le_rfl⟩
  have hfun : (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M m : ℝ)) = fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable m M.nu (Annealed.sigmaBar M m) (nativeSourceBandScalar m (ns + 1) 1 ω) := by
    funext ω
    have := native_source_band_trace_one M m (ns + 1) ω
    have hc : m + ((ns + 1 : ℕ) : ℤ) = m + 1 + (ns : ℤ) := by push_cast; ring
    rw [hc] at this
    exact this.symm
  rw [hfun]
  exact h1

/-- D1: the origin child cap in the old frame. -/
theorem nativeHeatStep_originChild_oldFrame_L20 (ns : ℕ) (hns9 : 9 ≤ ns)
    (hns160 : ns ≤ 160) (hind : NativeHeatStepIndivNum ns hns160) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun (Annealed.sigmaBar M m : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((min (nativeHeatOldRowGen ns).x (nativeHeatIndividualGen ns).1 : ℚ) : ℝ)) := by
  have ha := nativeHeatStep_originChild_individual ns hns9 hns160 hind M h hM hg m hpast hstate
  have hb := nativeHeatStep_originChild_oldRow ns hns9 hns160 hind M h hM hg m hpast hstate
  rcases le_total (nativeHeatOldRowGen ns).x (nativeHeatIndividualGen ns).1 with hc | hc
  · rw [min_eq_left hc]; exact hb
  · rw [min_eq_right hc]; exact ha

/-- The two block traces of an elliptic coarse response are strictly positive. -/
private theorem nativeHeatStepCC_trace_pos {Q : TriadicCube 2} {nu Lambda : ℝ}
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
private theorem nativeHeatStepCC_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hpos := nativeHeatStepCC_trace_pos hnu hEll
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

/-- Pathwise sharp frame map from `σ̄_m` to `σ̄_{m+1}` for the completed cutoff `N`. -/
theorem nativeHeatStep_sharpPathwise_cutoff (M : ABKModel 2) (m n N : ℤ)
    (omega : Cutoff.CutoffSample 2) :
    let rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ)
    let T0 : ℝ := traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu N omega).toFun (Annealed.sigmaBar M m : ℝ)
    traceDefect (cubeSet (originCube 2 n))
        (Cutoff.coefficientCutoff M.nu N omega).toFun (Annealed.sigmaBar M (m + 1) : ℝ) ≤
      (rho + rho⁻¹) / 2 * T0 + (rho - rho⁻¹) / 2 * Real.sqrt (T0 * (T0 + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
  dsimp only
  let A := coarseBlockMatrix (cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoff M.nu N omega).toFun
  let sigmaK : ℝ := Annealed.sigmaBar M m
  let sigmaM : ℝ := Annealed.sigmaBar M (m + 1)
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  obtain ⟨Lambda, hEll⟩ := cutoff_isEllipticFieldOn_cube M N omega (originCube 2 n)
  have htrpos := nativeHeatStepCC_trace_pos M.nu_pos hEll
  have hsigmaK : 0 < sigmaK := (Annealed.sigmaBar_characterization M m).1
  have hratio : 1 ≤ rho := by
    have h := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).1
    simpa [rho, sigmaK, sigmaM] using h
  have hx : 0 < x := mul_pos (inv_pos.mpr hsigmaK) htrpos.1
  have hy : 0 < y := mul_pos hsigmaK htrpos.2
  have hprod : 4 ≤ x * y := by
    have hp := nativeHeatStepCC_trace_product M.nu_pos hEll
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
  have hnew : traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu N omega).toFun sigmaM = x / rho + rho * y - 4 := by
    change sigmaM⁻¹ * Matrix.trace A.upperLeft +
      sigmaM * Matrix.trace A.lowerRight - 4 = _
    rw [← hxdiv, ← hydiv]
  have hold : traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu N omega).toFun sigmaK = x + y - 4 := by
    dsimp [x, y, sigmaK, A]
    unfold traceDefect
    field_simp [hsigmaK.ne']
  rw [hnew, hold]
  exact nativeHeatRefined_sharpFrameScalar hx hy hprod hratio

/-- D2: the sharp frame shift. -/
theorem nativeHeatStep_originChild_L20_le_y0 (ns : ℕ) (hns9 : 9 ≤ ns)
    (hns160 : ns ≤ 160) (hind : NativeHeatStepIndivNum ns hns160)
    (hfr : NativeHeatStepFrameNum ns) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M (m + 1) : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((nativeHeatY0Gen ns : ℚ) : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hL := nativeHeatStep_originChild_oldFrame_L20 ns hns9 hns160 hind M h hM hg m
    hpast hstate
  let tq : ℚ := nativeHeatShiftArgGen ns
  have htq : (min (nativeHeatOldRowGen ns).x (nativeHeatIndividualGen ns).1 : ℚ) = tq := rfl
  rw [htq] at hL
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun (Annealed.sigmaBar M m : ℝ)
  let Tn : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
        (Annealed.sigmaBar M (m + 1) : ℝ)
  have hT0 : ∀ ω, 0 ≤ T ω := by
    intro ω
    obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (m + 1 + (ns : ℤ)) ω (originCube 2 m)
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M m).1
  have hTn0 : ∀ ω, 0 ≤ Tn ω := by
    intro ω
    obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (m + 1 + (ns : ℤ)) ω (originCube 2 m)
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M (m + 1)).1
  have hTm : Measurable T := by
    have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives m M.nu
      (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        modelTraceObservable m M.nu (Annealed.sigmaBar M m)
          (nativeSourceBandScalar m (ns + 1) 1 ω)) :=
      hΦ.1.continuous.measurable.comp (native_source_band_scalar_measurable m (ns + 1) 1)
    convert hm using 1
    funext ω
    have := native_source_band_trace_one M m (ns + 1) ω
    have hc : m + ((ns + 1 : ℕ) : ℤ) = m + 1 + (ns : ℤ) := by push_cast; ring
    rw [hc] at this
    exact this.symm
  have hTnm : Measurable Tn := by
    have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives ((m + 1) - 1) M.nu
      (Annealed.sigmaBar M (m + 1)) M.nu_pos (Annealed.sigmaBar_characterization M (m + 1)).1
    have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        modelTraceObservable ((m + 1) - 1) M.nu (Annealed.sigmaBar M (m + 1))
          (nativeSourceChildBandScalar (m + 1) ns 1 ω)) :=
      hΦ.1.continuous.measurable.comp (native_source_child_band_scalar_measurable (m + 1) ns 1)
    convert hm using 1
    funext ω
    have := native_source_child_band_trace_one M (m + 1) ns ω
    have hrhs : traceDefect (cubeSet (originCube 2 ((m + 1) - 1)))
        (Cutoff.coefficientCutoff M.nu (m + 1 + (ns : ℤ)) ω).toFun
          (Annealed.sigmaBar M (m + 1) : ℝ) = Tn ω := by
      simp [Tn, Int.add_sub_cancel]
    exact (this.trans hrhs).symm
  set a : ℝ := (((11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) : ℚ) : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; norm_num [nativeGamma]
  have ha1 : a < 1 := by rw [ha]; norm_num [nativeGamma]
  set r : ℝ := 1 / (1 - a) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ (by linarith)]
    linarith
  have hrho := nativeHeatRefined_ratio_le M hg
  set c : ℝ := (r + r⁻¹) / 2
  set d : ℝ := (r - r⁻¹) / 2
  have hrpos : 0 < r := by linarith
  have hrinv0 : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hrinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hc0 : 0 ≤ c := by show 0 ≤ (r + r⁻¹) / 2; linarith
  have hd0 : 0 ≤ d := by show 0 ≤ (r - r⁻¹) / 2; linarith
  have hc1 : 1 ≤ c := by
    show 1 ≤ (r + r⁻¹) / 2
    have hmul : r * r⁻¹ = 1 := mul_inv_cancel₀ hrpos.ne'
    nlinarith [sq_nonneg (r - r⁻¹)]
  have hpt : ∀ ω, Tn ω ≤ c * T ω + d * Real.sqrt (T ω * (T ω + 8)) + 4 * (c - 1) := by
    intro ω
    have hp := nativeHeatStep_sharpPathwise_cutoff M m m (m + 1 + (ns : ℤ)) ω
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
    have hp' : Tn ω ≤
        (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
          4 * ((rho + rho⁻¹) / 2 - 1) := hp
    linarith
  have htq0 : (0 : ℝ) ≤ (tq : ℝ) := by
    have hv := heat_configured_individual_old_valid (nativeHeatIndexGen ns hns160)
    rw [hind.gap, hind.old_source] at hv
    have hx : (0 : ℚ) ≤ (nativeHeatOldRowGen ns).x := hv.2.1.le
    have hform := congrArg Prod.fst hind.indiv
    have hs := of_decide_eq_true hind.result20_root
    have hz := nativeConfiguredSystem_scale_pos (nativeHeatIndexGen ns hns160)
    have hA : (0 : ℚ) < nativeA := by norm_num [nativeA]
    have hprod : (0 : ℚ) ≤ nativeRootUp
        ((nativeConfiguredSystem (nativeHeatIndexGen ns hns160)).result.getD 20 0) 20 *
        (nativeConfiguredSystem (nativeHeatIndexGen ns hns160)).system.z * nativeA :=
      mul_nonneg (mul_nonneg hs.2.2.1 hz.le) hA.le
    have hi : (0 : ℚ) ≤ (nativeHeatIndividualGen ns).1 := by
      rw [hform]
      exact hprod.trans (nativeUp_ge _)
    have : (0 : ℚ) ≤ tq := le_min hx hi
    exact_mod_cast this
  have hfinal := nativeHeatRefined_eLpNorm'_frame_le hTm hTnm hT0 hTn0 hc0 hd0 (by linarith)
    htq0 hpt hL
  refine hfinal.trans (ENNReal.ofReal_le_ofReal ?_)
  have hd' : 0 ≤ (11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) ∧
      (11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) < 1 := by
    norm_num [nativeGamma]
  have hsound := nativeShiftedFrame_sound 1 tq hd' hfr.shift_root
  refine le_trans (le_of_eq ?_) hsound
  simp [nativeFrameReal, c, d, r, a, one_div, tq]

theorem nativeHeatStep_eLpNorm'_eq_of_map_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → ℝ} {g : β → ℝ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g ν) (hmap : Measure.map f μ = Measure.map g ν) (q : ℝ) :
    eLpNorm' f q μ = eLpNorm' g q ν := by
  have hm : Measurable (fun x : ℝ => ‖x‖ₑ ^ q) := by fun_prop
  unfold eLpNorm'
  congr 1
  rw [← lintegral_map' hm.aemeasurable hf, ← lintegral_map' hm.aemeasurable hg, hmap]

/-- The child trace at cutoff `N` and frame `σ`, as a function of the sample. -/
private theorem nativeHeatStepCC_child_aemeasurable (M : ABKModel 2) (N : ℤ) (Q : TriadicCube 2)
    (σ : ℝ) :
    AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω).toFun σ)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hF : AEMeasurable (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun σ)
      (Measure.map (Cutoff.coefficientCutoff M.nu N) (Cutoff.cutoffSampleLaw M).toMeasure) := by
    rw [← Cutoff.coefficientCutoffLaw_eq_map]
    exact Model.aemeasurable_traceDefect_cutoffLaw M N Q σ
  exact hF.comp_aemeasurable (Cutoff.measurable_coefficientCutoff M.nu N).aemeasurable

/-- Every cell of scale `m` has the same `L^20` trace norm as the origin cube. -/
theorem nativeHeatStep_cell_eLpNorm'_eq_origin (M : ABKModel 2) (N : ℤ) (Q : TriadicCube 2)
    (σ : ℝ) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu N ω).toFun σ) 20
      (Cutoff.cutoffSampleLaw M).toMeasure =
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 Q.scale)) (Cutoff.coefficientCutoff M.nu N ω).toFun σ) 20
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  refine nativeHeatStep_eLpNorm'_eq_of_map_eq (nativeHeatStepCC_child_aemeasurable M N Q σ)
    (nativeHeatStepCC_child_aemeasurable M N (originCube 2 Q.scale) σ) ?_ 20
  have h := Model.map_traceDefect_cube_eq_origin M N Q σ
  rw [Cutoff.coefficientCutoffLaw_eq_map] at h
  have hQ : AEMeasurable (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun σ)
      (Measure.map (Cutoff.coefficientCutoff M.nu N) (Cutoff.cutoffSampleLaw M).toMeasure) := by
    rw [← Cutoff.coefficientCutoffLaw_eq_map]
    exact Model.aemeasurable_traceDefect_cutoffLaw M N Q σ
  have hO : AEMeasurable (fun a : RegCoeffField 2 =>
      traceDefect (cubeSet (originCube 2 Q.scale)) a.toFun σ)
      (Measure.map (Cutoff.coefficientCutoff M.nu N) (Cutoff.cutoffSampleLaw M).toMeasure) := by
    rw [← Cutoff.coefficientCutoffLaw_eq_map]
    exact Model.aemeasurable_traceDefect_cutoffLaw M N _ σ
  have hc := (Cutoff.measurable_coefficientCutoff M.nu N).aemeasurable (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
  have e1 := AEMeasurable.map_map_of_aemeasurable hQ hc
  have e2 := AEMeasurable.map_map_of_aemeasurable hO hc
  exact e1.symm.trans (h.trans e2)

theorem nativeHeatStep_avg_const (K : ℕ) (hK : 0 < K) (y : ℝ) :
    ENNReal.ofReal (((K : ℝ))⁻¹) * ((K : ℕ) • ENNReal.ofReal y) = ENNReal.ofReal y := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hKR.le,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hKR.le)]
  congr 1
  field_simp

/-- The child trace of every refined cell has the direct cap `y₀`. -/
theorem nativeHeatStep_child_L20_le_y0 (ns : ℕ) (hns9 : 9 ≤ ns)
    (hns160 : ns ≤ 160) (hind : NativeHeatStepIndivNum ns hns160)
    (hfr : NativeHeatStepFrameNum ns) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 => nativeHeatStepChildTraceCC M m ns i ω) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal ((nativeHeatY0Gen ns : ℚ) : ℝ) := by
  have h0 := nativeHeatStep_originChild_L20_le_y0 ns hns9 hns160 hind hfr M h hM hg m hpast hstate
  have he := nativeHeatStep_cell_eLpNorm'_eq_origin M (m + 1 + (ns : ℤ))
    (nativeHeatQ3RefinedCarrierChild m i) (Annealed.sigmaBar M (m + 1) : ℝ)
  rw [nativeHeatQ3RefinedCarrierChild_scale] at he
  unfold nativeHeatStepChildTraceCC
  rw [he]
  exact h0

/-- The average of the refined child traces has the direct cap `y₀` (Minkowski). -/
theorem nativeHeatStep_childAverage_L20_le_y0 (ns : ℕ) (hns9 : 9 ≤ ns)
    (hns160 : ns ≤ 160) (hind : NativeHeatStepIndivNum ns hns160)
    (hfr : NativeHeatStepFrameNum ns) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      ((9 ^ 10 : ℝ)⁻¹) * Finset.univ.sum (fun i => nativeHeatStepChildTraceCC M m ns i ω)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal ((nativeHeatY0Gen ns : ℚ) : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let y : ℝ := ((nativeHeatY0Gen ns : ℚ) : ℝ)
  have hmeas (i : nativeHeatQ3RefinedCarrierIndex) :
      AEStronglyMeasurable (fun ω : Cutoff.CutoffSample 2 =>
        nativeHeatStepChildTraceCC M m ns i ω) μ :=
    (nativeHeatStepCC_child_aemeasurable M (m + 1 + (ns : ℤ)) _ _).aestronglyMeasurable
  have hchild (i : nativeHeatQ3RefinedCarrierIndex) :
      eLpNorm (fun ω : Cutoff.CutoffSample 2 => nativeHeatStepChildTraceCC M m ns i ω) 20 μ ≤
        ENNReal.ofReal y := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hmeas i)]
    simpa using nativeHeatStep_child_L20_le_y0 ns hns9 hns160 hind hfr M h hM hg m hpast
      hstate i
  have hsum : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      Finset.univ.sum (fun i => nativeHeatStepChildTraceCC M m ns i ω)) 20 μ ≤
      Finset.univ.sum (fun i : nativeHeatQ3RefinedCarrierIndex =>
        eLpNorm (fun ω : Cutoff.CutoffSample 2 => nativeHeatStepChildTraceCC M m ns i ω) 20 μ) := by
    have := eLpNorm_sum_le (μ := μ) (p := (20 : ℝ≥0∞)) (s := Finset.univ)
      (f := fun i ω => nativeHeatStepChildTraceCC M m ns i ω) (by norm_num)
    simpa [Finset.sum_fn] using this
  have hcard : (Finset.univ : Finset nativeHeatQ3RefinedCarrierIndex).card = 9 ^ 10 := by
    rw [Finset.card_univ]; exact nativeHeatQ3RefinedCarrierIndex_card
  have hscale : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      ((9 ^ 10 : ℝ)⁻¹) * Finset.univ.sum (fun i => nativeHeatStepChildTraceCC M m ns i ω)) 20 μ =
      ENNReal.ofReal ((9 ^ 10 : ℝ)⁻¹) * eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
        Finset.univ.sum (fun i => nativeHeatStepChildTraceCC M m ns i ω)) 20 μ := by
    have := eLpNorm_const_smul (μ := μ) (p := (20 : ℝ≥0∞)) ((9 ^ 10 : ℝ)⁻¹)
      (fun ω : Cutoff.CutoffSample 2 =>
        Finset.univ.sum (fun i => nativeHeatStepChildTraceCC M m ns i ω))
    simpa [Pi.smul_def, smul_eq_mul, Real.enorm_eq_ofReal (by positivity : (0:ℝ) ≤ (9 ^ 10 : ℝ)⁻¹)]
      using this
  rw [hscale]
  calc
    _ ≤ ENNReal.ofReal ((9 ^ 10 : ℝ)⁻¹) * Finset.univ.sum (fun i : nativeHeatQ3RefinedCarrierIndex =>
        eLpNorm (fun ω : Cutoff.CutoffSample 2 => nativeHeatStepChildTraceCC M m ns i ω) 20 μ) :=
      mul_le_mul' le_rfl hsum
    _ ≤ ENNReal.ofReal ((9 ^ 10 : ℝ)⁻¹) * Finset.univ.sum (fun _ : nativeHeatQ3RefinedCarrierIndex =>
        ENNReal.ofReal y) := mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hchild i)
    _ = ENNReal.ofReal y := by
      rw [Finset.sum_const, hcard]
      have := nativeHeatStep_avg_const (9 ^ 10) (by positivity) y
      rw [Nat.cast_pow, Nat.cast_ofNat] at this
      exact this

end ASDExplicitGamma.Native

end
