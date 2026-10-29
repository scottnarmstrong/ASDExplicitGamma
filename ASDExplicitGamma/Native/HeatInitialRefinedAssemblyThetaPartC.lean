module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssemblyThetaPartB
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

theorem nativeHeatRefined_initialMoment_ge_two_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
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
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ k * (nativeHeatInitialAt nativeHeatParametersData
          (nativeHeatGenQm ns) (nativeHeatGenVariance ns) k : ℝ)) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let qh := (k + 1) / 2
  let baseTerm : ℕ → ℚ := fun j =>
    (Nat.choose k j : ℚ) *
      nativeInitialMeanMoment nativeHeatParametersData (k - j) *
      (2 * nativeHeatB) ^ j * (nativeHeatGenQm ns).getD j 0
  let baseSumQ : ℚ := ((List.range (k + 1)).map baseTerm).sum
  let baseQ : ℚ := nativeUp baseSumQ
  let baseRootQ : ℚ := nativeRootUp baseQ k
  let innerRootQ : ℚ := nativeRootUp
    (nativeRootUp ((nativeHeatGenQm ns).getD qh 0) qh) 2
  let crossRawQ : ℚ := nativeHeatParametersData.cross.getD k 0 * innerRootQ
  let crossQ : ℚ := nativeUp crossRawQ
  let rareRawQ : ℚ :=
    2 * nativeHeatEps * nativeHeatParametersData.gm.getD k 0 * (nativeHeatGenVariance ns)
  let rareQ : ℚ := nativeUp rareRawQ
  let totalQ : ℚ := baseRootQ + crossQ + rareQ
  let A : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    nativeHeatRefinedOldAverage M m ω +
      2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω
  let C : Cutoff.CutoffSample 2 → ℝ := nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m
  let R : Cutoff.CutoffSample 2 → ℝ := nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m
  let Aabs : Cutoff.CutoffSample 2 → ℝ := fun ω => ‖A ω‖
  let Cabs : Cutoff.CutoffSample 2 → ℝ := fun ω => ‖C ω‖
  let Rabs : Cutoff.CutoffSample 2 → ℝ := fun ω => ‖R ω‖
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hbaseValid : nativeRootValid baseQ k = true := by
    simpa [baseQ, baseSumQ, baseTerm] using
      hnum.base k hk2 hk20
  have hbaseParts := of_decide_eq_true hbaseValid
  have hbaseRootNonneg : 0 ≤ (baseRootQ : ℝ) := by
    exact_mod_cast hbaseParts.2.2.1
  have hq1 : 1 ≤ qh := by dsimp [qh]; omega
  have hq10 : qh ≤ 10 := by dsimp [qh]; omega
  have hqOuterValid := hnum.outer qh hq1 hq10
  have hqOuterParts := of_decide_eq_true hqOuterValid
  have hinnerRootNonneg : 0 ≤ (innerRootQ : ℝ) := by
    exact_mod_cast hqOuterParts.2.2.1
  have hcrossParamNonneg :
      0 ≤ ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) :=
    nativeHeatCrossData_nonneg k hk2 hk20
  have hcrossRawNonneg : 0 ≤ (crossRawQ : ℝ) := by
    dsimp [crossRawQ]
    exact_mod_cast (mul_nonneg hcrossParamNonneg hinnerRootNonneg)
  have hcrossRootNonneg : 0 ≤ (crossQ : ℝ) := by
    have hround : (crossRawQ : ℝ) ≤ (crossQ : ℝ) := by
      dsimp [crossQ, crossRawQ]
      exact_mod_cast nativeUp_ge crossRawQ
    exact hcrossRawNonneg.trans hround
  have hgmNonneg : 0 ≤
      ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) :=
    nativeHeatInitialGM_nonneg k (by omega) hk20
  have hvarianceNonneg : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) := by
    exact_mod_cast hnum.variance_nonneg
  have hepsNonneg : 0 ≤ (nativeHeatEps : ℝ) := by
    norm_num [nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeEps]
  have hrareRawNonneg : 0 ≤ (rareRawQ : ℝ) := by
    dsimp [rareRawQ]
    exact_mod_cast (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num : (0 : ℝ) ≤ 2) hepsNonneg) hgmNonneg) hvarianceNonneg)
  have hrareRootNonneg : 0 ≤ (rareQ : ℝ) := by
    have hround : (rareRawQ : ℝ) ≤ (rareQ : ℝ) := by
      dsimp [rareQ, rareRawQ]
      exact_mod_cast nativeUp_ge rareRawQ
    exact hrareRawNonneg.trans hround
  have htotalNonneg : 0 ≤ (totalQ : ℝ) := by
    dsimp [totalQ]
    exact_mod_cast (add_nonneg (add_nonneg hbaseRootNonneg hcrossRootNonneg)
      hrareRootNonneg)
  have hAmeas : Measurable A := by
    dsimp [A]
    exact (nativeHeatRefinedOldAverage_measurable M m).add
      ((measurable_const : Measurable
        (fun _ : Cutoff.CutoffSample 2 => 2 * (nativeHeatB : ℝ))).mul
          (nativeHeatRefinedCenterQuadratic_measurable_Gen ns M m))
  have hYint := (nativeHeatRefined_centerQuadratic_integral_le_Theta ns hnum M m hGauss).1
  have hCint := (nativeHeatRefinedShearCross_integrable_zero_Gen ns M h hM hg m hpast hYint).1
  have hAes : AEStronglyMeasurable A μ := hAmeas.aestronglyMeasurable
  have hCes : AEStronglyMeasurable C μ := hCint.aestronglyMeasurable
  have hRes : AEStronglyMeasurable R μ :=
    (nativeHeatRefinedRare_measurable_Gen ns M h hM hg m hpast).aestronglyMeasurable
  have hAabsMeas : AEStronglyMeasurable Aabs μ := hAes.norm
  have hCabsMeas : AEStronglyMeasurable Cabs μ := hCes.norm
  have hRabsMeas : AEStronglyMeasurable Rabs μ := hRes.norm
  have hA_lp := nativeHeatRefined_initialBaseLp_Theta ns hnum
    M h hM hg m hpast hGauss k hk2 hk20
  have hC_lp := nativeHeatRefined_initialCrossLp_Theta ns hnum M h hM m hCross k hk2 hk20
  have hR_lp := nativeHeatRefined_initialRareLp_Theta ns hnum M h hM m hRare k hk2 hk20
  have hcomponents : ∀ᵐ ω ∂μ,
      nativeHeatRefinedObservableGen ns M m ω ≤ A ω + C ω + R ω := by
    filter_upwards [nativeHeatRefinedObservable_le_components_Gen ns
      M h hM hg m hpast] with ω hω
    simpa [A, C, R] using hω
  have hOmono : ∀ᵐ ω ∂μ,
      ‖nativeHeatRefinedObservableGen ns M m ω‖ ≤ Aabs ω + Cabs ω + Rabs ω := by
    filter_upwards [hcomponents] with ω hω
    have hOpos := nativeHeatRefinedObservable_nonneg_Gen ns M m ω
    have htri : A ω + C ω + R ω ≤
        ‖A ω‖ + ‖C ω‖ + ‖R ω‖ := by
      calc
        _ ≤ |A ω + C ω + R ω| := le_abs_self _
        _ ≤ |A ω + C ω| + |R ω| := abs_add_le _ _
        _ ≤ (|A ω| + |C ω|) + |R ω| :=
          add_le_add (abs_add_le _ _) (le_refl _)
        _ = _ := by simp [Real.norm_eq_abs, add_assoc]
    rw [Real.norm_of_nonneg hOpos]
    calc
      nativeHeatRefinedObservableGen ns M m ω ≤ A ω + C ω + R ω := hω
      _ ≤ ‖A ω‖ + ‖C ω‖ + ‖R ω‖ := htri
      _ = Aabs ω + Cabs ω + Rabs ω := by rfl
  have hLp := nativeHeatInitialLp_three_le
    (nativeHeatRefinedObservableGen ns M m) Aabs Cabs Rabs (k : ℝ)
    (ENNReal.ofReal (theta M * (baseRootQ : ℝ))) (ENNReal.ofReal (theta M * (crossQ : ℝ)))
    (ENNReal.ofReal (theta M * (rareQ : ℝ)))
    hkpos hk1R hAabsMeas hCabsMeas hRabsMeas
    (fun ω => norm_nonneg _) (fun ω => norm_nonneg _) (fun ω => norm_nonneg _)
    hOmono hA_lp hC_lp hR_lp
  have hsumCaps :
      ENNReal.ofReal (theta M * (baseRootQ : ℝ)) + ENNReal.ofReal (theta M * (crossQ : ℝ)) +
        ENNReal.ofReal (theta M * (rareQ : ℝ)) = ENNReal.ofReal (theta M * (totalQ : ℝ)) := by
    have hb0 := mul_nonneg hτ0.le hbaseRootNonneg
    have hc0 := mul_nonneg hτ0.le hcrossRootNonneg
    have hr0 := mul_nonneg hτ0.le hrareRootNonneg
    calc
      _ = ENNReal.ofReal (theta M * (baseRootQ : ℝ) + theta M * (crossQ : ℝ)) +
          ENNReal.ofReal (theta M * (rareQ : ℝ)) := by
        rw [ENNReal.ofReal_add hb0 hc0]
      _ = ENNReal.ofReal ((theta M * (baseRootQ : ℝ) + theta M * (crossQ : ℝ)) +
            theta M * (rareQ : ℝ)) := by
        rw [ENNReal.ofReal_add (add_nonneg hb0 hc0) hr0]
      _ = ENNReal.ofReal (theta M * (totalQ : ℝ)) := by
        congr 1
        simp only [totalQ]
        push_cast
        ring
  have htotalLp : eLpNorm' (nativeHeatRefinedObservableGen ns M m)
      (k : ℝ) μ ≤ ENNReal.ofReal (theta M * (totalQ : ℝ)) := by
    calc
      _ ≤ ENNReal.ofReal (theta M * (baseRootQ : ℝ)) + ENNReal.ofReal (theta M * (crossQ : ℝ)) +
          ENNReal.ofReal (theta M * (rareQ : ℝ)) := hLp
      _ = ENNReal.ofReal (theta M * (totalQ : ℝ)) := hsumCaps
  have hrow : nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
      (nativeHeatGenVariance ns) k = nativeUp (totalQ ^ k) := by
    have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp [nativeHeatInitialAt, hk0, hk1, baseQ, baseSumQ, baseTerm, baseRootQ,
      innerRootQ, crossRawQ, crossQ, rareRawQ, rareQ, totalQ, qh]
  calc
    _ = (eLpNorm' (nativeHeatRefinedObservableGen ns M m) (k : ℝ) μ) ^ (k : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
    _ ≤ (ENNReal.ofReal (theta M * (totalQ : ℝ))) ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow htotalLp (by positivity)
    _ = ENNReal.ofReal ((theta M * (totalQ : ℝ)) ^ k) := by
      rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (mul_nonneg hτ0.le htotalNonneg)]
    _ ≤ ENNReal.ofReal (theta M ^ k * (nativeUp (totalQ ^ k) : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast nativeUp_ge (totalQ ^ k))
        (pow_nonneg hτ0.le _)
    _ = ENNReal.ofReal (theta M ^ k *
        (nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
          (nativeHeatGenVariance ns) k : ℝ)) := by rw [hrow]


end

end ASDExplicitGamma.Native
