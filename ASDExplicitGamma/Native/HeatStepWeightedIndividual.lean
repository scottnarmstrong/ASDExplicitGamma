module

public import ASDExplicitGamma.Native.HeatStepChildCap
public import ASDExplicitGamma.Native.HeatIndividualComparisonW

/-! The weighted-amplitude individual cap: for every amplitude vector `W` the `L^20` norm of the
trace of the weighted band at its endpoint `s = 1`, in the frame `σ̄_q`, obeys the individual
cooperative bound of the gap `ns + 1` system. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped ENNReal
open ASDExplicitGamma.Gaussian

theorem nativeHeatStep_weighted_individual (ns : ℕ) (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hind : NativeHeatStepIndivNum ns hns160) (W : NativeAmp) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (hstate : nativeInductionState M h m) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable m M.nu (Annealed.sigmaBar M m)
        (nativeSourceBandScalar_W W m (ns + 1) 1 ω))
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
  let X : Cutoff.CutoffSample 2 → ℝ := fun ω => Φ (nativeSourceBandScalar_W W m g 1 ω)
  have hgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨C, hC, d, hd, _⟩ := hΦ.2
    exact ⟨C, hC, d, hd⟩
  have hmeasΦ : Measurable Φ := hΦ.1.continuous.measurable
  have hmem : MemLp X (ENNReal.ofReal 20) μ :=
    native_source_band_test_memLp_W (W := W) M h hM m g hg1 Φ hmeasΦ hgrowth 1 20 (by norm_num)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => hΦ0 _
  have hcomp := native_individual_cooperative_comparison_W (W := W) M h hM hg m hpast hstate idx 1
    ⟨zero_le_one, le_rfl⟩ 20
  have hcurve : nativeIndividualMomentCurve_W W M m idx 1 20 = ∫ ω, X ω ^ 20 ∂μ := by
    simp only [nativeIndividualMomentCurve_W, nativeSourceBandMomentK_W, nativeSourceBandAverage_W]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [X, Φ, g, Real.rpow_natCast]
  have hz : (0 : ℝ) < ((nativeConfiguredSystem idx).system.z : ℝ) := by
    exact_mod_cast nativeConfiguredSystem_scale_pos idx
  have hmom : (∫ ω, X ω ^ 20 ∂μ) ≤
      (3 / 50 : ℝ) ^ 20 * ((nativeConfiguredSystem idx).system.z : ℝ) ^ 20 *
        nativeVectorReal (nativeConfiguredSystem idx).result 20 := by
    have hn := hcomp
    simp only [nativeIndividualNormalizedMomentCurve_W, nativeConfiguredNormalizedMomentCurve,
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
  have hfunX : (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable m M.nu (Annealed.sigmaBar M m)
        (nativeSourceBandScalar_W W m (ns + 1) 1 ω)) = X := by
    funext ω
    simp only [X, Φ]
    rw [← hgap]
  rw [hfunX]
  calc
    eLpNorm' X 20 μ = (∫⁻ ω, ‖X ω‖ₑ ^ (20 : ℝ) ∂μ) ^ (1 / (20 : ℝ)) := rfl
    _ = (ENNReal.ofReal A) ^ (1 / (20 : ℝ)) := by rw [hlin]
    _ = ENNReal.ofReal (A ^ ((20 : ℝ)⁻¹)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num), one_div]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hrootA.trans hind')

end ASDExplicitGamma.Native
