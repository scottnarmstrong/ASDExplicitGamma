module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssemblyThetaPartA
public import ASDExplicitGamma.Native.HeatInitialRefinedMeanMomentTheta
public import ASDExplicitGamma.Native.HeatInitialThetaGaussian
public import ASDExplicitGamma.Native.HeatInitialThetaRare
public import ASDExplicitGamma.Native.HeatInitialRefinedCrossProviderTheta

/-! Theta-scaled Hölder/root-sum assembly of the refined initial heat row: the base, cross and
rare `L^k` caps carry the factor `θ`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators
set_option linter.constructorNameAsVariable false

noncomputable section

theorem nativeHeatRefined_centerQuadratic_integral_le_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2)
    (m : ℤ)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))) :
    Integrable (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
  have hτ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m
  have hYNonneg := nativeHeatRefinedCenterQuadratic_nonneg_Gen ns M m
  have hmoment := hGauss 1 le_rfl (by norm_num)
  have hmoment' : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤
      ENNReal.ofReal (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
    have hq1 : ((nativeHeatGenQm ns)[1]?.getD 0) = nativeHeatGenVariance ns := by
      simpa using nativeHeatGenQm_getD_one ns
    simpa [Y, μ, hq1] using hmoment
  have hfinite : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hmoment' ENNReal.ofReal_lt_top
  have hYmeas : Measurable Y := by
    dsimp [Y]
    exact nativeHeatRefinedCenterQuadratic_measurable_Gen ns M m
  have hYInt : Integrable Y μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hYmeas.aestronglyMeasurable (Filter.Eventually.of_forall hYNonneg)).mp hfinite
  have hreal : ENNReal.ofReal (∫ ω, Y ω ∂μ) ≤
      ENNReal.ofReal (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hYInt
      (Filter.Eventually.of_forall hYNonneg)]
    exact hmoment'
  have hvariance : 0 ≤ (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
    exact mul_nonneg hτ0 (by exact_mod_cast hnum.variance_nonneg)
  exact ⟨hYInt, (ENNReal.ofReal_le_ofReal_iff hvariance).mp hreal⟩

theorem nativeHeatRefined_rareQuadratic_integral_le_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)))) ^ (k : ℝ)) :
    Integrable (nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        2 * (nativeHeatEps : ℝ) * (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
  have hτ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m
  have hRNonneg := nativeHeatRefinedRare_nonneg_Gen ns M h hM hg m hpast
  have hmoment := hRare 1 le_rfl (by norm_num)
  have hmeasR : Measurable R := nativeHeatRefinedRare_measurable_Gen ns M h hM hg m hpast
  have hmoment2 : ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ∂μ ≤
      ENNReal.ofReal (2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ))))) := by
    simpa [μ, mul_assoc] using hmoment
  have hmoment' : ∫⁻ ω, ‖R ω‖ₑ ∂μ ≤ ENNReal.ofReal
      (2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ))))) := by
    simpa [R, μ] using hmoment2
  have hfinite : ∫⁻ ω, ENNReal.ofReal (R ω) ∂μ ≠ ∞ := by
    apply ne_of_lt
    calc
      ∫⁻ ω, ENNReal.ofReal (R ω) ∂μ ≤ ∫⁻ ω, ‖R ω‖ₑ ∂μ := by
        apply lintegral_mono
        intro ω
        exact le_of_eq (Real.enorm_eq_ofReal (hRNonneg ω)).symm
      _ ≤ ENNReal.ofReal
          (2 * ((inverseBankReserve .localInverse : ℝ) *
            (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
              (theta M * ((nativeHeatGenVariance ns) : ℝ))))) := hmoment'
      _ < ∞ := ENNReal.ofReal_lt_top
  have hRInt : Integrable R μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmeasR.aestronglyMeasurable (Filter.Eventually.of_forall hRNonneg)).mp hfinite
  have hreal : ENNReal.ofReal (∫ ω, R ω ∂μ) ≤ ENNReal.ofReal
      (2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ))))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hRInt
      (Filter.Eventually.of_forall hRNonneg)]
    calc
      ∫⁻ ω, ENNReal.ofReal (R ω) ∂μ ≤ ∫⁻ ω, ‖R ω‖ₑ ∂μ := by
        apply lintegral_mono
        intro ω
        exact le_of_eq (Real.enorm_eq_ofReal (hRNonneg ω)).symm
      _ ≤ ENNReal.ofReal
          (2 * ((inverseBankReserve .localInverse : ℝ) *
            (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
              (theta M * ((nativeHeatGenVariance ns) : ℝ))))) := hmoment'
  have hcapNonneg : 0 ≤ 2 * ((inverseBankReserve .localInverse : ℝ) *
      (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
        (theta M * ((nativeHeatGenVariance ns) : ℝ)))) := by
    have hgmNonneg : 0 ≤ ((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) :=
      nativeHeatInitialGM_nonneg 1 (by norm_num) (by norm_num)
    have hreserve : 0 ≤ (inverseBankReserve .localInverse : ℝ) := by
      norm_num [inverseBankReserve]
    have hv : 0 ≤ (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
      exact mul_nonneg hτ0 (by exact_mod_cast hnum.variance_nonneg)
    exact mul_nonneg (by norm_num) (mul_nonneg hreserve (mul_nonneg hgmNonneg hv))
  have hRbound : ∫ ω, R ω ∂μ ≤
      2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)))) :=
    (ENNReal.ofReal_le_ofReal_iff hcapNonneg).mp hreal
  have hreserveGM : (inverseBankReserve .localInverse : ℚ) *
      nativeHeatParametersData.gm.getD 1 0 ≤ nativeHeatEps := by
    rw [← nativeHeatGM01_formula]
    norm_num [inverseBankReserve, nativeHeatEps, nativeHeatRQ, nativeE,
      nativeGamma, nativeEps, nativeRootUp, nativeRootCandidate,
      nativeRootScale]
  have hreserveGMReal : (inverseBankReserve .localInverse : ℝ) *
      ((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) ≤
        (nativeHeatEps : ℝ) := by
    exact_mod_cast hreserveGM
  have hvariance : 0 ≤ (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
    exact mul_nonneg hτ0 (by exact_mod_cast hnum.variance_nonneg)
  have hcap : 2 * ((inverseBankReserve .localInverse : ℝ) *
      (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
        (theta M * ((nativeHeatGenVariance ns) : ℝ)))) ≤
      2 * (nativeHeatEps : ℝ) * (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hreserveGMReal hvariance
    nlinarith [hmul]
  exact ⟨hRInt, hRbound.trans hcap⟩


theorem nativeHeatRefined_initialFirstMoment_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)))) ^ (k : ℝ)) :
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * (nativeUp
        (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
          (nativeHeatGenVariance ns)) : ℝ)) := by
  have hτ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let old := nativeHeatRefinedOldAverage M m
  let Y := nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m
  let C := nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m
  let R := nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m
  let F : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    old ω + 2 * (nativeHeatB : ℝ) * Y ω + C ω + R ω
  have hOld : Integrable old μ ∧ ∫ ω, old ω ∂μ ≤ theta M * (nativeQstar : ℝ) := by
    obtain ⟨hint, hmeanEq, hmeanLe⟩ :=
      nativeHeatRefinedOldAverage_mean_theta M h hM hg m hpast
    exact ⟨hint, hmeanEq ▸ hmeanLe⟩
  have hY := nativeHeatRefined_centerQuadratic_integral_le_Theta ns hnum M m hGauss
  have hR := nativeHeatRefined_rareQuadratic_integral_le_Theta ns hnum M h hM hg m hpast hRare
  have hCC := nativeHeatRefinedShearCross_integrable_zero_Gen ns M h hM hg m hpast hY.1
  have hCInt : Integrable C μ := hCC.1
  have hCzero : ∫ ω, C ω ∂μ = 0 := hCC.2
  have hFInt : Integrable F μ := by
    dsimp [F]
    exact ((hOld.1.add (hY.1.const_mul _)).add hCInt).add hR.1
  have hFmean : ∫ ω, F ω ∂μ =
      (∫ ω, old ω ∂μ) + 2 * (nativeHeatB : ℝ) *
        (∫ ω, Y ω ∂μ) + (∫ ω, C ω ∂μ) + (∫ ω, R ω ∂μ) := by
    have hOY : Integrable (fun ω => old ω + 2 * (nativeHeatB : ℝ) * Y ω) μ :=
      hOld.1.add (hY.1.const_mul _)
    have hOYC : Integrable
        (fun ω => old ω + 2 * (nativeHeatB : ℝ) * Y ω + C ω) μ :=
      hOY.add hCInt
    calc
      ∫ ω, F ω ∂μ =
          (∫ ω, old ω + 2 * (nativeHeatB : ℝ) * Y ω + C ω ∂μ) +
            ∫ ω, R ω ∂μ := by
              exact integral_add hOYC hR.1
      _ = ((∫ ω, old ω ∂μ) +
            ∫ ω, 2 * (nativeHeatB : ℝ) * Y ω ∂μ) +
            ∫ ω, C ω ∂μ + ∫ ω, R ω ∂μ := by
              rw [integral_add hOY hCInt, integral_add hOld.1 (hY.1.const_mul _)]
      _ = _ := by rw [integral_const_mul]
  have hBnonneg : 0 ≤ 2 * (nativeHeatB : ℝ) := by
    norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
  have hYscaled : 2 * (nativeHeatB : ℝ) * (∫ ω, Y ω ∂μ) ≤
      2 * (nativeHeatB : ℝ) * (theta M * ((nativeHeatGenVariance ns) : ℝ)) :=
    mul_le_mul_of_nonneg_left hY.2 hBnonneg
  have hFbound : ∫ ω, F ω ∂μ ≤
      theta M * (nativeQstar : ℝ) +
        2 * ((nativeHeatB : ℝ) + (nativeHeatEps : ℝ)) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)) := by
    rw [hFmean, hCzero]
    nlinarith [hOld.2, hYscaled, hR.2]
  have hcomponents : ∀ᵐ ω ∂μ, nativeHeatRefinedObservableGen ns M m ω ≤ F ω := by
    filter_upwards [nativeHeatRefinedObservable_le_components_Gen ns
      M h hM hg m hpast] with ω hω
    simpa [F, old, Y, C, R] using hω
  have hFnonneg : 0 ≤ᵐ[μ] F := by
    filter_upwards [hcomponents] with ω hω
    exact (nativeHeatRefinedObservable_nonneg_Gen ns M m ω).trans
      (by simpa [F, old, Y, C, R] using hω)
  have hlintegral :
      ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hcomponents] with ω hω
    have hO := nativeHeatRefinedObservable_nonneg_Gen ns M m ω
    have hle : nativeHeatRefinedObservableGen ns M m ω ≤ F ω := by
      simpa [F, old, Y, C, R] using hω
    calc
      ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ =
          ENNReal.ofReal (nativeHeatRefinedObservableGen ns M m ω) := by
            exact Real.enorm_eq_ofReal hO
      _ ≤ ENNReal.ofReal (F ω) := ENNReal.ofReal_le_ofReal hle
  calc
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ := hlintegral
    _ = ENNReal.ofReal (∫ ω, F ω ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hFInt hFnonneg).symm
    _ ≤ ENNReal.ofReal
        (theta M * (nativeQstar : ℝ) +
          2 * ((nativeHeatB : ℝ) + (nativeHeatEps : ℝ)) *
            (theta M * ((nativeHeatGenVariance ns) : ℝ))) := ENNReal.ofReal_le_ofReal hFbound
    _ ≤ ENNReal.ofReal (theta M * (nativeUp
        (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
          (nativeHeatGenVariance ns)) : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have hup : (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
            (nativeHeatGenVariance ns) : ℝ) ≤ (nativeUp
          (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
            (nativeHeatGenVariance ns)) : ℝ) := by
          exact_mod_cast nativeUp_ge
            (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
              (nativeHeatGenVariance ns))
        nlinarith [mul_le_mul_of_nonneg_left hup hτ0]


end

end ASDExplicitGamma.Native
