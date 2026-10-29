module

public import ASDExplicitGamma.Native.HeatInitialRefinedFrame
public import ASDExplicitGamma.Native.HeatIndividualThetaComparison
public import ASDExplicitGamma.Native.HeatStepAllTimeFrameTheta
public import ASDExplicitGamma.Native.HeatInitialRefinedChildCapTheta

/-! Theta-scaled old-frame `L^20` cap of the lag `-1` child and its source cap `θ · hp`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Variational ASDExplicitGamma.Response
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal

/-- The old-frame lag-minus-one trace at the completed cutoff `m+1`: `L²⁰` cap from the
gap-one individual cooperative system. -/
theorem nativeHeatRefined_oldFrame_L20_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ j < m, nativeInductionState M h j)
    (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * ((nativeGap001Individual.1 : ℚ) : ℝ)) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
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
  have hcomp := native_individual_cooperative_comparison_theta_W (W := NativeAmp.one) M h hM hg m
    hpast hstate 0 1 ⟨zero_le_one, le_rfl⟩ 20
  have hcurve : nativeIndividualMomentCurve_W NativeAmp.one M m 0 1 20 = ∫ ω, X ω ^ 20 ∂μ := by
    simp only [nativeIndividualMomentCurve_W, nativeSourceBandMomentK_W,
      nativeSourceBandAverage_W]
    have hgap : (nativeConfiguredSystem 0).gap = 1 := rfl
    rw [hgap]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [X, Φ, Real.rpow_natCast, ← nativeSourceBandScalar_eq_W_one]
  have hz : (0 : ℝ) < ((nativeConfiguredSystem 0).system.z : ℝ) := by
    exact_mod_cast nativeConfiguredSystem_scale_pos 0
  have hmom : (∫ ω, X ω ^ 20 ∂μ) ≤ theta M ^ 20 *
      ((3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem 0).system.z : ℝ) ^ 20 *
        nativeVectorReal (nativeConfiguredSystem 0).result 20) := by
    have hn := hcomp
    simp only [nativeConfiguredNormalizedMomentCurve, nativeIndividualMomentCurveTheta_W,
      hcurve] at hn
    have h20 : (20 : Fin 21).val ≠ 0 := by decide
    have hv : (20 : Fin 21).val = 20 := rfl
    simp only [h20, ite_false, hv] at hn
    have hpos : 0 < theta M ^ 20 * ((3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem 0).system.z : ℝ) ^ 20) := by
      positivity
    rw [if_neg (by norm_num : (20:ℕ) ≠ 0)] at hn
    rw [div_div, div_le_iff₀ hpos] at hn
    calc _ ≤ _ := hn
      _ = _ := by ring
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
  have hrootA : A ^ ((20 : ℝ)⁻¹) ≤ theta M *
      ((3 / 50 : ℝ) * ((nativeConfiguredSystem 0).system.z : ℝ) *
        (nativeRootUp (nativeGap001Result.getD 20 0) 20 : ℝ)) := by
    have hB := Real.rpow_le_rpow hA0 hmom (by norm_num : (0 : ℝ) ≤ (20 : ℝ)⁻¹)
    refine hB.trans ?_
    have h0 : ((theta M) ^ 20) ^ ((20 : ℝ)⁻¹) = theta M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ0.le]
      norm_num
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hres,
      Real.mul_rpow (by positivity) (by positivity), h0]
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
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hrootA.trans (mul_le_mul_of_nonneg_left hind hτ0.le))


/-- The refined lag-minus-one child trace has the theta-scaled source `L²⁰` cap `θ · hp`. -/
theorem nativeHeatRefined_childTrace_L20_le_hp_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ j < m + 1, nativeInductionState M h j) :
    eLpNorm' (cutoffTraceDefect M (m + 1) m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  have hL := nativeHeatRefined_oldFrame_L20_theta M h hM hg m
    (fun j hj => hpast j (by omega)) (hpast m (by omega))
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun (Annealed.sigmaBar M m : ℝ)
  have hT0 : ∀ ω, 0 ≤ T ω := by
    intro ω
    obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (m + 1) ω (originCube 2 m)
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M m).1
  have hTm : Measurable T := nativeHeatRefined_oldFrameTrace_measurable M m
  have hTn : Measurable (cutoffTraceDefect M (m + 1) m) :=
    Variational.cutoffTraceDefect_measurable M (m + 1) m
  have hpath : ∀ ω, let rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ)
      cutoffTraceDefect M (m + 1) m ω ≤ (rho + rho⁻¹) / 2 * T ω +
        (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) + 4 * ((rho + rho⁻¹) / 2 - 1) := by
    intro ω
    exact nativeHeatRefined_sharpPathwise M m m ω
  have hvalid : nativeRootValid (nativeGap001Individual.1 * (nativeGap001Individual.1 + 8)) 2 = true := by
    decide +kernel
  have hind0 : (0 : ℝ) ≤ ((nativeGap001Individual.1 : ℚ) : ℝ) := by
    norm_num [nativeGap001Individual]
  have hfr := nativeHeatStep_frameTransfer_theta M hg m T (cutoffTraceDefect M (m + 1) m)
    hTm hTn hT0 (cutoffTraceDefect_nonneg M (m + 1) m) hpath nativeGap001Individual.1 hind0 hvalid hL
  have hmin : min nativeGap001Old.x nativeGap001Individual.1 = nativeGap001Individual.1 := by
    apply min_eq_right
    decide +kernel
  have hHP := nativeHeatHP_formula
  rw [hmin] at hHP
  rw [← hHP]
  exact hfr

end ASDExplicitGamma.Native
