module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssemblyGen
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

/-- The independent old-average and fresh-center contribution fits the
binomial base of the configured native initial row. -/
theorem nativeHeatRefined_baseMoment_le_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)))
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedOldAverage M m ω +
        2 * (nativeHeatB : ℝ) *
          nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M ^ k * ∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) *
          (nativeInitialMeanMoment nativeHeatParametersData (k - j) : ℝ) *
          (2 * (nativeHeatB : ℝ)) ^ j *
          (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let X : Cutoff.CutoffSample 2 → ℝ := nativeHeatRefinedOldAverage M m
  let Y : Cutoff.CutoffSample 2 → ℝ :=
    nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m
  have hXmeas : Measurable X := nativeHeatRefinedOldAverage_measurable M m
  have hYmeas : Measurable Y := nativeHeatRefinedCenterQuadratic_measurable_Gen ns M m
  have hXnonneg := nativeHeatRefinedOldAverage_nonneg M m
  have hYnonneg := nativeHeatRefinedCenterQuadratic_nonneg_Gen ns M m
  have hIndep : IndepFun X Y μ := nativeHeatRefinedOldFresh_independent_Gen ns M m
  have hA_nonneg (n : ℕ) (hn : n ≤ k) :
      0 ≤ theta M ^ n * (nativeInitialMeanMoment nativeHeatParametersData n : ℝ) := by
    have : (0 : ℝ) ≤ (nativeInitialMeanMoment nativeHeatParametersData n : ℝ) := by
      exact_mod_cast nativeInitialMeanMoment_nonneg n
    positivity
  have hB_nonneg (j : ℕ) (hj : j ≤ k) :
      0 ≤ theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) := by
    have : (0 : ℝ) ≤ (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) := by
      exact_mod_cast hnum.qm_nonneg j (le_trans hj hk20)
    positivity
  have hXmom (n : ℕ) (hn : n ≤ k) :
      ∫⁻ ω, ‖X ω‖ₑ ^ (n : ℝ) ∂μ ≤
        ENNReal.ofReal (theta M ^ n * (nativeInitialMeanMoment nativeHeatParametersData n : ℝ)) :=
    nativeHeatRefinedOldAverage_moment_le_theta M h hM hg m hpast n (le_trans hn hk20)
  have hYmom (j : ℕ) (hj : j ≤ k) :
      ∫⁻ ω, ‖Y ω‖ₑ ^ (j : ℝ) ∂μ ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) := by
    by_cases hj0 : j = 0
    · subst j
      have h0 : ((nativeHeatGenQm ns)[0]?.getD 0) = 1 := by
        have := nativeHeatGenQm_getD_zero ns
        simpa using this
      simp [Y, μ, h0]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hfresh := hGauss j hj1 (le_trans hj hk20)
      have hpoint (ω : Cutoff.CutoffSample 2) :
          ‖Y ω‖ₑ ^ (j : ℝ) = ENNReal.ofReal (Y ω ^ j) := by
        rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal (hYnonneg ω),
          ENNReal.ofReal_pow (hYnonneg ω)]
      rw [lintegral_congr hpoint]
      exact hfresh
  have hc : 0 ≤ 2 * (nativeHeatB : ℝ) := by
    norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
  have key := nativeHeat_independent_nonneg_add_moment_of_caps
    X Y hXmeas hYmeas hIndep hXnonneg hYnonneg (2 * (nativeHeatB : ℝ)) hc k
    (fun n => theta M ^ n * (nativeInitialMeanMoment nativeHeatParametersData n : ℝ))
    (fun j => theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    hA_nonneg hB_nonneg hXmom hYmom
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : theta M ^ (k - j) * theta M ^ j = theta M ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hjk]
  calc (Nat.choose k j : ℝ) * (theta M ^ (k - j) * (nativeInitialMeanMoment nativeHeatParametersData (k - j) : ℝ)) *
        (2 * (nativeHeatB : ℝ)) ^ j * (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
      = (theta M ^ (k - j) * theta M ^ j) * ((Nat.choose k j : ℝ) *
          (nativeInitialMeanMoment nativeHeatParametersData (k - j) : ℝ) *
          (2 * (nativeHeatB : ℝ)) ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) := by ring
    _ = _ := by rw [hpow]


theorem nativeHeatRefined_initialBaseLp_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (theta M ^ j * (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      ‖nativeHeatRefinedOldAverage M m ω +
        2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω‖)
      (k : ℝ) ((Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (theta M * (nativeRootUp (nativeUp
          (((List.range (k + 1)).map fun j =>
            (Nat.choose k j : ℚ) *
              nativeInitialMeanMoment nativeHeatParametersData (k - j) *
              (2 * nativeHeatB) ^ j * (nativeHeatGenQm ns).getD j 0).sum)) k : ℝ)) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let baseTerm : ℕ → ℚ := fun j =>
    (Nat.choose k j : ℚ) *
      nativeInitialMeanMoment nativeHeatParametersData (k - j) *
      (2 * nativeHeatB) ^ j * (nativeHeatGenQm ns).getD j 0
  let baseSumQ : ℚ := ((List.range (k + 1)).map baseTerm).sum
  let baseQ : ℚ := nativeUp baseSumQ
  let baseRootQ : ℚ := nativeRootUp baseQ k
  let A : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    nativeHeatRefinedOldAverage M m ω +
      2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω
  let Aabs : Cutoff.CutoffSample 2 → ℝ := fun ω => ‖A ω‖
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hbaseValid : nativeRootValid baseQ k = true := by
    simpa [baseQ, baseSumQ, baseTerm] using
      hnum.base k hk2 hk20
  have hbaseParts := of_decide_eq_true hbaseValid
  have hbaseRootNonneg : 0 ≤ (baseRootQ : ℝ) := by
    exact_mod_cast hbaseParts.2.2.1
  have hbaseRootPower : (baseSumQ : ℝ) ≤ (baseRootQ : ℝ) ^ k := by
    have hroundQ : baseSumQ ≤ baseQ := by
      dsimp [baseQ]
      exact nativeUp_ge baseSumQ
    have hroundR : (baseSumQ : ℝ) ≤ (baseQ : ℝ) := by exact_mod_cast hroundQ
    have hrootR : (baseQ : ℝ) ≤ (baseRootQ : ℝ) ^ k := by
      exact_mod_cast hbaseParts.2.2.2
    exact hroundR.trans hrootR
  have hbaseSumReal : (baseSumQ : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) *
          (nativeInitialMeanMoment nativeHeatParametersData (k - j) : ℝ) *
          (2 * (nativeHeatB : ℝ)) ^ j *
          (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) := by
    calc
      (baseSumQ : ℝ) =
          ((((List.range (k + 1)).map baseTerm).sum : ℚ) : ℝ) := rfl
      _ = ∑ j ∈ Finset.range (k + 1), (baseTerm j : ℝ) := by
        exact_mod_cast nativeHeatInitial_listSum_eq_finsetSum baseTerm (k + 1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [baseTerm, Rat.cast_mul]
  have hbaseCap : ENNReal.ofReal (theta M ^ k * (baseSumQ : ℝ)) ≤
      (ENNReal.ofReal (theta M * (baseRootQ : ℝ))) ^ (k : ℝ) := by
    calc
      ENNReal.ofReal (theta M ^ k * (baseSumQ : ℝ)) ≤
          ENNReal.ofReal ((theta M * (baseRootQ : ℝ)) ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hbaseRootPower (pow_nonneg hτ0.le _)
      _ = (ENNReal.ofReal (theta M * (baseRootQ : ℝ))) ^ (k : ℝ) := by
        rw [ENNReal.ofReal_pow (mul_nonneg hτ0.le hbaseRootNonneg), ENNReal.rpow_natCast]
  have hmoment := nativeHeatRefined_baseMoment_le_Theta ns hnum
    M h hM hg m hpast hGauss k hk20
  have hmomentAbs :
      ∫⁻ ω, ‖Aabs ω‖ₑ ^ (k : ℝ) ∂μ ≤ ENNReal.ofReal (theta M ^ k * (baseSumQ : ℝ)) := by
    simpa [Aabs, A, μ, hbaseSumReal] using hmoment
  exact nativeHeatInitialLp_of_moment Aabs (k : ℝ) (theta M * (baseRootQ : ℝ)) hkpos
    (hmomentAbs.trans hbaseCap)


theorem nativeHeatRefined_initialCrossLp_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal (theta M * ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ))) ^
            (k : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖) (k : ℝ)
      ((Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (theta M *
          ((nativeUp (nativeHeatParametersData.cross.getD k 0 *
            nativeRootUp (nativeRootUp
              ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2) : ℚ) : ℝ)) := by
  have hτ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let qh := (k + 1) / 2
  let innerRootQ := nativeRootUp
    (nativeRootUp ((nativeHeatGenQm ns).getD qh 0) qh) 2
  let crossRawQ := nativeHeatParametersData.cross.getD k 0 * innerRootQ
  let crossQ := nativeUp crossRawQ
  let Cabs : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hround : (crossRawQ : ℝ) ≤ (crossQ : ℝ) := by
    dsimp [crossQ, crossRawQ]
    exact_mod_cast nativeUp_ge crossRawQ
  have hcap : (ENNReal.ofReal (theta M * (crossRawQ : ℝ))) ^ (k : ℝ) ≤
      (ENNReal.ofReal (theta M * (crossQ : ℝ))) ^ (k : ℝ) :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hround hτ0))
      (by positivity)
  have hmoment := hCross k hk2 hk20
  have hmomentAbs :
      ∫⁻ ω, ‖Cabs ω‖ₑ ^ (k : ℝ) ∂μ ≤
        (ENNReal.ofReal (theta M * (crossRawQ : ℝ))) ^ (k : ℝ) := by
    simpa [Cabs, μ, qh, innerRootQ, crossRawQ] using hmoment
  have hlp := nativeHeatInitialLp_of_moment Cabs (k : ℝ) (theta M * (crossQ : ℝ)) hkpos
    (hmomentAbs.trans hcap)
  change eLpNorm' Cabs (k : ℝ) μ ≤ ENNReal.ofReal (theta M * (crossQ : ℝ))
  exact hlp


theorem nativeHeatRefined_initialRareLp_Theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (theta M * ((nativeHeatGenVariance ns) : ℝ)))) ^ (k : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖) (k : ℝ)
      ((Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (theta M *
          ((nativeUp
            (2 * nativeHeatEps * nativeHeatParametersData.gm.getD k 0 *
              (nativeHeatGenVariance ns)) : ℚ) : ℝ)) := by
  have hτ0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let rareRawQ : ℚ :=
    2 * nativeHeatEps * nativeHeatParametersData.gm.getD k 0 * (nativeHeatGenVariance ns)
  let rareQ : ℚ := nativeUp rareRawQ
  let Rabs : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖
  let reserveCapR : ℝ := 2 * (inverseBankReserve .localInverse : ℝ) *
    ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
      (theta M * ((nativeHeatGenVariance ns) : ℝ))
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ k := by omega
  have hgmNonneg : 0 ≤
      ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) :=
    nativeHeatInitialGM_nonneg k hk1 hk20
  have hvarianceNonneg : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) := by
    exact_mod_cast hnum.variance_nonneg
  have hreserve :
      (inverseBankReserve .localInverse : ℝ) ≤ (nativeHeatEps : ℝ) := by
    norm_num [inverseBankReserve, nativeHeatEps, nativeHeatRQ, nativeE,
      nativeGamma, nativeEps]
  have hrawCompare : reserveCapR ≤ theta M * (rareRawQ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hreserve
      (mul_nonneg hgmNonneg hvarianceNonneg)
    have hm2 := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)
    have hm3 := mul_le_mul_of_nonneg_left hm2 hτ0
    calc
      reserveCapR = theta M * (2 * ((inverseBankReserve .localInverse : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ)))) := by
        dsimp [reserveCapR]
        ring
      _ ≤ theta M * (2 * ((nativeHeatEps : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ)))) := hm3
      _ = theta M * (rareRawQ : ℝ) := by
        dsimp [rareRawQ]
        push_cast
        ring
  have hround : (rareRawQ : ℝ) ≤ (rareQ : ℝ) := by
    dsimp [rareQ, rareRawQ]
    exact_mod_cast nativeUp_ge rareRawQ
  have hcap : (ENNReal.ofReal reserveCapR) ^ (k : ℝ) ≤
      (ENNReal.ofReal (theta M * (rareQ : ℝ))) ^ (k : ℝ) := by
    have hrawLe : ENNReal.ofReal reserveCapR ≤ ENNReal.ofReal (theta M * (rareRawQ : ℝ)) :=
      ENNReal.ofReal_le_ofReal hrawCompare
    exact (ENNReal.rpow_le_rpow hrawLe (by positivity)).trans
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hround hτ0)) (by positivity))
  have hmoment := hRare k hk1 hk20
  have hCapEq : (2 * (inverseBankReserve .localInverse : ℝ) *
      (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
        (theta M * ((nativeHeatGenVariance ns) : ℝ)))) = reserveCapR := by
    dsimp [reserveCapR]
    ring
  have hmomentAbs :
      ∫⁻ ω, ‖Rabs ω‖ₑ ^ (k : ℝ) ∂μ ≤
        (ENNReal.ofReal reserveCapR) ^ (k : ℝ) := by
    rw [← hCapEq]
    simpa [Rabs, μ] using hmoment
  have hlp := nativeHeatInitialLp_of_moment Rabs (k : ℝ) (theta M * (rareQ : ℝ)) hkpos
    (hmomentAbs.trans hcap)
  change eLpNorm' Rabs (k : ℝ) μ ≤ ENNReal.ofReal (theta M * (rareQ : ℝ))
  exact hlp


end

end ASDExplicitGamma.Native
