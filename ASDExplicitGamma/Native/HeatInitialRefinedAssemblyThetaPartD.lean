module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssemblyThetaPartC
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

/-- Every refined initial row, from the three component rows. -/
theorem nativeHeatRefined_initialMoment_of_providers_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)))
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal (theta M * ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ))) ^
            (k : ℝ))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)))) ^ (k : ℝ))
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ k * (nativeHeatInitialAt nativeHeatParametersData
          (nativeHeatGenQm ns) (nativeHeatGenVariance ns) k : ℝ)) := by
  by_cases hk0 : k = 0
  · subst k
    letI : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
      (Cutoff.cutoffSampleLaw M).property
    simp [nativeHeatInitialAt]
  · by_cases hk1 : k = 1
    · subst k
      simpa [nativeHeatInitialAt] using
        nativeHeatRefined_initialFirstMoment_Theta ns hnum M h hM hg m hpast hGauss hRare
    · have hk2 : 2 ≤ k := by omega
      exact nativeHeatRefined_initialMoment_ge_two_Theta ns hnum
        M h hM hg m hpast hGauss hCross hRare k hk2 hk20


/-- Conditional refined initial row at the carrier. -/
theorem nativeHeatQ3RefinedCarrierSourceInitialMoment_of_providers_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)))
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal (theta M * ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ))) ^
            (k : ℝ))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)))) ^ (k : ℝ))
    (k : ℕ) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k (nativeHeatTheta : ℝ) 0 ≤
      theta M ^ k * ((nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
        (nativeHeatGenVariance ns) k : ℚ) : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  rw [nativeHeatRefined_sourceMoment_zero_eq_integral_Gen]
  have hrow := nativeHeatRefined_initialMoment_of_providers_Theta ns hnum M h hM hg m hpast
    hGauss hCross hRare k hk20
  have hnonneg : ∀ ω, 0 ≤ (nativeHeatRefinedObservableGen ns M m ω) ^ k :=
    fun ω => pow_nonneg (nativeHeatRefinedObservable_nonneg_Gen ns M m ω) k
  have hcapQ : (0 : ℚ) ≤ nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
      (nativeHeatGenVariance ns) k := by
    by_cases hk0 : k = 0
    · subst k; norm_num [nativeHeatInitialAt]
    by_cases hk1 : k = 1
    · subst k
      unfold nativeHeatInitialAt
      simp only [one_ne_zero, if_false, if_true]
      refine le_trans ?_ (nativeUp_ge _)
      have hVn := hnum.variance_nonneg
      norm_num [nativeHeatB, nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeB,
        nativeEps, nativeQstar]
      first | positivity | nlinarith [hVn] | linarith
    have hk2 : 2 ≤ k := by omega
    unfold nativeHeatInitialAt
    simp only [hk0, hk1, if_false]
    refine le_trans ?_ (nativeUp_ge _)
    refine pow_nonneg ?_ k
    have hroot := nativeHeatRootUp_nonneg
    refine add_nonneg (add_nonneg (hroot _ _) ?_) ?_
    · refine le_trans ?_ (nativeUp_ge _)
      have hcr : (0 : ℚ) ≤ nativeHeatParametersData.cross.getD k 0 := by
        have := nativeHeatCrossData_nonneg k hk2 hk20
        exact_mod_cast this
      exact mul_nonneg hcr (hroot _ _)
    · refine le_trans ?_ (nativeUp_ge _)
      have hgm : (0 : ℚ) ≤ nativeHeatParametersData.gm.getD k 0 := by
        have := nativeHeatInitialGM_nonneg k (by omega) hk20
        exact_mod_cast this
      have hEps : (0 : ℚ) ≤ nativeHeatEps := by
        norm_num [nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeEps]
      have hV : (0 : ℚ) ≤ (nativeHeatGenVariance ns) := by exact_mod_cast hnum.variance_nonneg
      positivity
  have hcap : (0 : ℝ) ≤ theta M ^ k * ((nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
      (nativeHeatGenVariance ns) k : ℚ) : ℝ) :=
    mul_nonneg (pow_nonneg hτ0.le _) (by exact_mod_cast hcapQ)
  by_cases hint : Integrable (fun ω => (nativeHeatRefinedObservableGen ns M m ω) ^ k) μ
  · have h1 := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnonneg)
    have h2 : ∫⁻ ω, ENNReal.ofReal ((nativeHeatRefinedObservableGen ns M m ω) ^ k) ∂μ =
        ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ^ (k : ℝ) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal (nativeHeatRefinedObservable_nonneg_Gen ns M m ω),
        ENNReal.ofReal_pow (nativeHeatRefinedObservable_nonneg_Gen ns M m ω)]
    rw [h2] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hcap).mp (h1.trans_le hrow)
  · rw [integral_undef hint]
    exact hcap


end

end ASDExplicitGamma.Native
