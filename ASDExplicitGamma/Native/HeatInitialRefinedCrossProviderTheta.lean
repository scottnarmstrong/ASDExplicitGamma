module

public import ASDExplicitGamma.Native.HeatInitialRefinedCrossGen
public import ASDExplicitGamma.Native.HeatInitialRefinedCrossTheta
public import ASDExplicitGamma.Native.HeatInitialThetaGaussian

/-! The theta-scaled shear cross row for `ns` shells: `θ · cross_k · rootroot(qm)`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory
open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped BigOperators ENNReal
set_option linter.constructorNameAsVariable false

/-- Outward roots turn an interpolated RMS moment bound into the generated cap. -/
theorem nativeHeat_rms_capTheta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns) (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) {τ : ℝ} (hτ : 0 ≤ τ) {X : ℝ≥0∞}
    (hMoment : X ≤ (ENNReal.ofReal (τ ^ ((k + 1) / 2) * (((nativeHeatGenQm ns).getD ((k + 1) / 2) 0 : ℚ) : ℝ))) ^
      ((k : ℝ) / (2 * (((k + 1) / 2 : ℕ) : ℝ)))) :
    X ≤ (ENNReal.ofReal (Real.sqrt τ * ((nativeRootUp
      (nativeRootUp ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ))) ^
        (k : ℝ) := by
  let q : ℕ := (k + 1) / 2
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq10 : q ≤ 10 := by dsimp [q]; omega
  have hq20 : q ≤ 20 := by omega
  have hk2q : k ≤ 2 * q := by dsimp [q]; omega
  let v : ℚ := (nativeHeatGenQm ns).getD q 0
  let u : ℚ := nativeRootUp v q
  let cap : ℚ := nativeRootUp u 2
  have hvValid := hnum.qroot q hq1 hq10
  have huValid := hnum.outer q hq1 hq10
  have hvData : 0 < q ∧ 0 ≤ v ∧ 0 ≤ u ∧ v ≤ u ^ q := by
    simpa [v, u] using of_decide_eq_true hvValid
  have huValid' : nativeRootValid u 2 = true := by
    simpa [v, u] using huValid
  have huData : 0 < 2 ∧ 0 ≤ u ∧ 0 ≤ cap ∧ u ≤ cap ^ 2 := by
    exact of_decide_eq_true huValid'
  have hvcap : v ≤ cap ^ (2 * q) := by
    calc
      v ≤ u ^ q := hvData.2.2.2
      _ ≤ (cap ^ 2) ^ q := pow_le_pow_left₀ huData.2.1 huData.2.2.2 q
      _ = cap ^ (2 * q) := by rw [← pow_mul]
  have hvcapReal : (v : ℝ) ≤ (cap : ℝ) ^ (2 * (q : ℝ)) := by
    exact_mod_cast hvcap
  have hcapReal0 : 0 ≤ (cap : ℝ) := by exact_mod_cast huData.2.2.1
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrootExpNonneg : 0 ≤ 2 * (q : ℝ) := mul_nonneg (by norm_num) hqRpos.le
  have hsq : Real.sqrt τ ^ (2 * q) = τ ^ q := by
    rw [pow_mul, Real.sq_sqrt hτ]
  have hbase : ENNReal.ofReal (τ ^ q * (v : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt τ * (cap : ℝ)) ^ (2 * (q : ℝ)) := by
    calc
      ENNReal.ofReal (τ ^ q * (v : ℝ)) ≤
          ENNReal.ofReal ((Real.sqrt τ * (cap : ℝ)) ^ (2 * (q : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          mul_pow, hsq]
        have hq' : (v : ℝ) ≤ (cap : ℝ) ^ (2 * q) := by
          have := hvcapReal
          rwa [show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at this
        exact mul_le_mul_of_nonneg_left hq' (pow_nonneg hτ _)
      _ = ENNReal.ofReal (Real.sqrt τ * (cap : ℝ)) ^ (2 * (q : ℝ)) :=
        (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcapReal0) hrootExpNonneg).symm
  have hexp : 0 ≤ (k : ℝ) / (2 * (q : ℝ)) := by positivity
  have hpower := ENNReal.rpow_le_rpow hbase hexp
  have hflat :
      (ENNReal.ofReal (Real.sqrt τ * (cap : ℝ)) ^ (2 * (q : ℝ))) ^
          ((k : ℝ) / (2 * (q : ℝ))) =
        ENNReal.ofReal (Real.sqrt τ * (cap : ℝ)) ^ (k : ℝ) := by
    have hExpEq : (2 * (q : ℝ)) * ((k : ℝ) / (2 * (q : ℝ))) = (k : ℝ) := by
      field_simp
    rw [← ENNReal.rpow_mul, hExpEq]
  have hpower' : (ENNReal.ofReal (τ ^ q * (v : ℝ))) ^ ((k : ℝ) / (2 * (q : ℝ))) ≤
      ENNReal.ofReal (Real.sqrt τ * (cap : ℝ)) ^ (k : ℝ) := by
    rw [← hflat]
    exact hpower
  have hresult := hMoment.trans hpower'
  simpa [q, v, u, cap] using hresult

/-- RMS moments of the refined centre vector, from its quadratic moment row. -/
theorem nativeHeatRefined_fresh_rms_momentTheta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hstate : nativeInductionState M h (m + 1))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, (ENNReal.ofReal (Real.sqrt
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω))) ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal (Real.sqrt (theta M) * ((nativeRootUp
        (nativeRootUp ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ))) ^
          (k : ℝ) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let F := nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m
  let q : ℕ := (k + 1) / 2
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq20 : q ≤ 20 := by dsimp [q]; omega
  have hk2q : k ≤ 2 * q := by dsimp [q]; omega
  have hF0 : ∀ ω, 0 ≤ F ω := nativeHeatRefined_centerQuadratic_nonnegGen ns M m
  have hFmeas : Measurable F := nativeHeatRefined_centerQuadratic_measurableGen ns M m
  have hlin := nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_theta ns hnum
    M h hM hg m hstate q hq20
  have hfin : ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ < ∞ :=
    lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hintPow : Integrable (fun ω => F ω ^ q) μ := by
    refine ⟨(hFmeas.pow_const q).aestronglyMeasurable, ?_⟩
    have : ∀ ω, ‖F ω ^ q‖ₑ = ENNReal.ofReal (F ω ^ q) := fun ω =>
      Real.enorm_eq_ofReal (pow_nonneg (hF0 ω) q)
    simp only [HasFiniteIntegral, this]
    exact hfin
  have hFmem : MemLp F (ENNReal.ofReal (q : ℝ)) μ := by
    have hnat : MemLp F (q : ℝ≥0∞) μ := by
      have h1 : Integrable (fun ω => ‖F ω‖ ^ (((q : ℝ≥0∞)).toReal)) μ := by
        simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
        have heq : (fun ω => ‖F ω‖ ^ q) = fun ω => F ω ^ q := by
          funext ω
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
        rw [heq]
        exact hintPow
      exact (integrable_norm_rpow_iff hFmeas.aestronglyMeasurable
        (by simp; omega) (by simp)).mp h1
    simpa using hnat
  have hMomentReal : ∫ ω, F ω ^ q ∂μ ≤ theta M ^ q * (((nativeHeatGenQm ns).getD q 0 : ℚ) : ℝ) := by
    have h1 : ENNReal.ofReal (∫ ω, F ω ^ q ∂μ) = ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hintPow
        (Filter.Eventually.of_forall fun ω => pow_nonneg (hF0 ω) q)
    have h2 : ENNReal.ofReal (∫ ω, F ω ^ q ∂μ) ≤
        ENNReal.ofReal (theta M ^ q * (((nativeHeatGenQm ns).getD q 0 : ℚ) : ℝ)) := by
      rw [h1]; exact hlin
    have hnn : (0 : ℝ) ≤ theta M ^ q * (((nativeHeatGenQm ns).getD q 0 : ℚ) : ℝ) := by
      have := hnum.qm_nonneg q (by omega)
      have : (0 : ℝ) ≤ (((nativeHeatGenQm ns).getD q 0 : ℚ) : ℝ) := by exact_mod_cast this
      positivity
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2
  have hrms := nativeHeat_lintegral_sqrt_rpow_le_of_moment F q k hq1 hk2 hk2q hF0
    hFmem (theta M ^ q * (((nativeHeatGenQm ns).getD q 0 : ℚ) : ℝ)) hMomentReal
  exact nativeHeat_rms_capTheta ns hnum k hk2 hk20 hτ0.le hrms

/-- The refined shear-cross bound. -/
theorem nativeHeatQ3RefinedCarrierSourceShearCrossMoment_theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal (theta M * ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ))) ^
            (k : ℝ) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hgamma
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ι := nativeHeatQ3RefinedCarrierIndex
  let C : ι → TriadicCube 2 := nativeHeatQ3RefinedCarrierChild m
  let J : Set ℤ := Set.Icc (m + 2) (m + ns + 1)
  let Fresh : Cutoff.CutoffSample 2 → ι → ℝ := fun ω i =>
    nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i
  let coeff : ι → (ι → ℝ) → ℝ := fun i η => η i
  haveI : Nonempty ι := ⟨⟨0, by norm_num⟩⟩
  have hJ : Disjoint (Set.Iic (m + 1)) J := by
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with ⟨hzLo, hzHi⟩
    change z ≤ m + 1 at hz
    omega
  have hFreshMeas : Measurable Fresh :=
    measurable_pi_iff.mpr fun i => nativeHeatQ3RefinedZ_measurableGen ns M m i
  have hFreshLocal : @Measurable (Cutoff.CutoffSample 2) (ι → ℝ)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance Fresh := by
    refine (@measurable_pi_iff (Cutoff.CutoffSample 2) ι (fun _ => ℝ)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) (fun _ => inferInstance)).mpr ?_
    intro i
    exact nativeHeatQ3RefinedZ_shellLocalGen ns M m i
  have hcoeff (i : ι) : Measurable (coeff i) := measurable_pi_apply i
  let q : ℕ := (k + 1) / 2
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq10 : q ≤ 10 := by dsimp [q]; omega
  let freshCap : ℝ := Real.sqrt (theta M) * ((nativeRootUp (nativeRootUp ((nativeHeatGenQm ns).getD q 0) q) 2 : ℚ) : ℝ)
  have hcap : 0 ≤ freshCap := by
    refine mul_nonneg (Real.sqrt_nonneg _) ?_
    exact_mod_cast nativeHeat_generatedCap_nonnegGen ns hnum q hq1 hq10
  have hRmeas : Measurable (fun η : ι → ℝ =>
      (ENNReal.ofReal (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ *
        ∑ i : ι, (coeff i η) ^ 2))) ^ (k : ℝ)) := by
    have hsum : Measurable (fun η : ι → ℝ => ∑ i : ι, (coeff i η) ^ 2) := by
      apply Finset.measurable_sum
      intro i _
      exact (hcoeff i).pow_const 2
    exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp
        (Real.continuous_sqrt.measurable.comp (measurable_const.mul hsum)))
  have hfresh :
      ∫⁻ η, (ENNReal.ofReal (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ *
        ∑ i : ι, (coeff i η) ^ 2))) ^ (k : ℝ) ∂(μ.map Fresh) ≤
        (ENNReal.ofReal freshCap) ^ (k : ℝ) := by
    calc
      _ = ∫⁻ ω, (ENNReal.ofReal (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ *
          ∑ i : ι, (coeff i (Fresh ω)) ^ 2))) ^ (k : ℝ) ∂μ := by
        rw [MeasureTheory.lintegral_map hRmeas hFreshMeas]
      _ = ∫⁻ ω, (ENNReal.ofReal (Real.sqrt
          (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω))) ^ (k : ℝ) ∂μ := by
        apply lintegral_congr
        intro ω
        rfl
      _ ≤ _ := nativeHeatRefined_fresh_rms_momentTheta ns hnum M h hM hgamma m hstate k hk2 hk20
  have hmain := nativeHeatRefined_oldShear_fresh_average_initialCrossMoment_theta M h hM hgamma m C
    (nativeHeatQ3RefinedCarrierChild_injective m) nativeHeatQ3RefinedCarrierIndex_card
    (fun i => nativeHeatQ3RefinedCarrierChild_scale m i) J hJ k hk2 hk20 hpast
    hFreshLocal hFreshMeas coeff hcoeff freshCap hcap hfresh
  have hcongr : ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ) ∂μ =
      ∫⁻ ω, ‖(2 * (∑ i, coeff i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))) /
          (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ) ∂μ := by
    apply lintegral_congr
    intro ω
    unfold nativeHeatQ3RefinedCarrierSourceShearCrossGen
    congr 2
    rw [div_eq_inv_mul]
    simp only [coeff, Fresh, C, ι]
    ring
  rw [hcongr]
  refine hmain.trans (le_of_eq ?_)
  congr 2
  simp only [freshCap]
  have hsqθ : Real.sqrt (theta M) * Real.sqrt (theta M) = theta M := Real.mul_self_sqrt hτ0.le
  calc Real.sqrt (theta M) * (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
        (Real.sqrt (theta M) * ((nativeRootUp (nativeRootUp ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)))
      = (Real.sqrt (theta M) * Real.sqrt (theta M)) * (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
          ((nativeRootUp (nativeRootUp ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) := by ring
    _ = _ := by rw [hsqθ]

end ASDExplicitGamma.Native
