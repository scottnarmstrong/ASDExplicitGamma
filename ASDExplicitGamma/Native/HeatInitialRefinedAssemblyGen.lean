module

public import ASDExplicitGamma.Native.HeatInitialRefinedAssembly
public import ASDExplicitGamma.Native.HeatInitialRefinedStartGen
public import ASDExplicitGamma.Native.HeatInitialRefinedSplitGen
public import ASDExplicitGamma.Native.HeatInitialRefinedIndepGen
public import ASDExplicitGamma.Native.HeatInitialNumericsStructGen

/-! The Hölder and root-sum assembly of the refined initial heat row for `ns` shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators
set_option linter.constructorNameAsVariable false


noncomputable section

theorem nativeHeatRefinedCenterQuadratic_nonneg_Gen (ns : ℕ) [NeZero ns] (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- The independent old-average and fresh-center contribution fits the
binomial base of the configured native initial row. -/
theorem nativeHeatRefined_baseMoment_le_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedOldAverage M m ω +
        2 * (nativeHeatB : ℝ) *
          nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) *
          (nativeInitialMeanMoment nativeHeatParametersData (k - j) : ℝ) *
          (2 * (nativeHeatB : ℝ)) ^ j *
          (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) := by
  classical
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
      0 ≤ (nativeInitialMeanMoment nativeHeatParametersData n : ℝ) := by
    exact_mod_cast nativeInitialMeanMoment_nonneg n
  have hB_nonneg (j : ℕ) (hj : j ≤ k) :
      0 ≤ (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) := by
    exact_mod_cast hnum.qm_nonneg j (le_trans hj hk20)
  have hXmom (n : ℕ) (hn : n ≤ k) :
      ∫⁻ ω, ‖X ω‖ₑ ^ (n : ℝ) ∂μ ≤
        ENNReal.ofReal (nativeInitialMeanMoment nativeHeatParametersData n : ℝ) :=
    nativeHeatRefinedOldAverage_moment_le M h hM hg m hpast n (le_trans hn hk20)
  have hYmom (j : ℕ) (hj : j ≤ k) :
      ∫⁻ ω, ‖Y ω‖ₑ ^ (j : ℝ) ∂μ ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ) := by
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
  exact nativeHeat_independent_nonneg_add_moment_of_caps
    X Y hXmeas hYmeas hIndep hXnonneg hYnonneg (2 * (nativeHeatB : ℝ)) hc k
    (fun n => (nativeInitialMeanMoment nativeHeatParametersData n : ℝ))
    (fun j => (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) hA_nonneg hB_nonneg hXmom hYmom

theorem nativeHeatRefined_initialBaseLp_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      ‖nativeHeatRefinedOldAverage M m ω +
        2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω‖)
      (k : ℝ) ((Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (nativeRootUp (nativeUp
          (((List.range (k + 1)).map fun j =>
            (Nat.choose k j : ℚ) *
              nativeInitialMeanMoment nativeHeatParametersData (k - j) *
              (2 * nativeHeatB) ^ j * (nativeHeatGenQm ns).getD j 0).sum)) k : ℝ) := by
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
  have hbaseCap : ENNReal.ofReal (baseSumQ : ℝ) ≤
      (ENNReal.ofReal (baseRootQ : ℝ)) ^ (k : ℝ) := by
    calc
      ENNReal.ofReal (baseSumQ : ℝ) ≤
          ENNReal.ofReal ((baseRootQ : ℝ) ^ k) :=
        ENNReal.ofReal_le_ofReal hbaseRootPower
      _ = (ENNReal.ofReal (baseRootQ : ℝ)) ^ (k : ℝ) := by
        rw [ENNReal.ofReal_pow hbaseRootNonneg, ENNReal.rpow_natCast]
  have hmoment := nativeHeatRefined_baseMoment_le_Gen ns hnum
    M h hM hg m hpast hGauss k hk20
  have hmomentAbs :
      ∫⁻ ω, ‖Aabs ω‖ₑ ^ (k : ℝ) ∂μ ≤ ENNReal.ofReal (baseSumQ : ℝ) := by
    simpa [Aabs, A, μ, hbaseSumReal] using hmoment
  exact nativeHeatInitialLp_of_moment Aabs (k : ℝ) (baseRootQ : ℝ) hkpos
    (hmomentAbs.trans hbaseCap)

theorem nativeHeatRefined_initialCrossLp_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
            (k : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖) (k : ℝ)
      ((Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal
          ((nativeUp (nativeHeatParametersData.cross.getD k 0 *
            nativeRootUp (nativeRootUp
              ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2) : ℚ) : ℝ) := by
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
  have hcap : (ENNReal.ofReal (crossRawQ : ℝ)) ^ (k : ℝ) ≤
      (ENNReal.ofReal (crossQ : ℝ)) ^ (k : ℝ) :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hround) (by positivity)
  have hmoment := hCross k hk2 hk20
  have hmomentAbs :
      ∫⁻ ω, ‖Cabs ω‖ₑ ^ (k : ℝ) ∂μ ≤
        (ENNReal.ofReal (crossRawQ : ℝ)) ^ (k : ℝ) := by
    simpa [Cabs, μ, qh, innerRootQ, crossRawQ] using hmoment
  have hlp := nativeHeatInitialLp_of_moment Cabs (k : ℝ) (crossQ : ℝ) hkpos
    (hmomentAbs.trans hcap)
  change eLpNorm' Cabs (k : ℝ) μ ≤ ENNReal.ofReal (crossQ : ℝ)
  exact hlp

theorem nativeHeatRefined_initialRareLp_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖) (k : ℝ)
      ((Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ENNReal.ofReal
          ((nativeUp
            (2 * nativeHeatEps * nativeHeatParametersData.gm.getD k 0 *
              (nativeHeatGenVariance ns)) : ℚ) : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let rareRawQ : ℚ :=
    2 * nativeHeatEps * nativeHeatParametersData.gm.getD k 0 * (nativeHeatGenVariance ns)
  let rareQ : ℚ := nativeUp rareRawQ
  let Rabs : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖
  let reserveCapR : ℝ := 2 * (inverseBankReserve .localInverse : ℝ) *
    ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
      ((nativeHeatGenVariance ns) : ℝ)
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
  have hrawCompare : reserveCapR ≤ (rareRawQ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hreserve
      (mul_nonneg hgmNonneg hvarianceNonneg)
    have hm2 := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)
    calc
      reserveCapR = 2 * ((inverseBankReserve .localInverse : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ))) := by
        dsimp [reserveCapR]
        ring
      _ ≤ 2 * ((nativeHeatEps : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ))) := hm2
      _ = (rareRawQ : ℝ) := by
        dsimp [rareRawQ]
        push_cast
        ring
  have hround : (rareRawQ : ℝ) ≤ (rareQ : ℝ) := by
    dsimp [rareQ, rareRawQ]
    exact_mod_cast nativeUp_ge rareRawQ
  have hcap : (ENNReal.ofReal reserveCapR) ^ (k : ℝ) ≤
      (ENNReal.ofReal (rareQ : ℝ)) ^ (k : ℝ) := by
    have hrawLe : ENNReal.ofReal reserveCapR ≤ ENNReal.ofReal (rareRawQ : ℝ) :=
      ENNReal.ofReal_le_ofReal hrawCompare
    exact (ENNReal.rpow_le_rpow hrawLe (by positivity)).trans
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hround) (by positivity))
  have hmoment := hRare k hk1 hk20
  have hCapEq : (2 * (inverseBankReserve .localInverse : ℝ) *
      (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
        ((nativeHeatGenVariance ns) : ℝ))) = reserveCapR := by
    dsimp [reserveCapR]
    ring
  have hmomentAbs :
      ∫⁻ ω, ‖Rabs ω‖ₑ ^ (k : ℝ) ∂μ ≤
        (ENNReal.ofReal reserveCapR) ^ (k : ℝ) := by
    rw [← hCapEq]
    simpa [Rabs, μ] using hmoment
  have hlp := nativeHeatInitialLp_of_moment Rabs (k : ℝ) (rareQ : ℝ) hkpos
    (hmomentAbs.trans hcap)
  change eLpNorm' Rabs (k : ℝ) μ ≤ ENNReal.ofReal (rareQ : ℝ)
  exact hlp

theorem nativeHeatRefinedRare_nonneg_Gen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω := by
  unfold nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen
  refine mul_nonneg (by norm_num) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => ?_))
  have hprofile := nativeHeatOldInverseTraceProfileD4_of_states M h hM hg
    (nativeHeatQ3RefinedCarrierChild m i) (m + 1)
    (by have := nativeHeatQ3RefinedCarrierChild_scale m i; omega) hpast
  exact mul_nonneg (hprofile.2.1 ω) (sq_nonneg _)

theorem nativeHeatRefinedRare_measurable_Gen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n) :
    Measurable (nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m) := by
  unfold nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen
  refine measurable_const.mul (measurable_const.mul
    (Finset.measurable_sum _ fun i _ => ?_))
  have hprofile := nativeHeatOldInverseTraceProfileD4_of_states M h hM hg
    (nativeHeatQ3RefinedCarrierChild m i) (m + 1)
    (by have := nativeHeatQ3RefinedCarrierChild_scale m i; omega) hpast
  exact hprofile.1.mul ((nativeHeatRefinedZ_measurable_Gen ns M m i).pow_const 2)

theorem nativeHeatRefined_centerQuadratic_integral_le_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2)
    (m : ℤ)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ)) :
    Integrable (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ((nativeHeatGenVariance ns) : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m
  have hYNonneg := nativeHeatRefinedCenterQuadratic_nonneg_Gen ns M m
  have hmoment := hGauss 1 le_rfl (by norm_num)
  have hmoment' : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤
      ENNReal.ofReal ((nativeHeatGenVariance ns) : ℝ) := by
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
      ENNReal.ofReal ((nativeHeatGenVariance ns) : ℝ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hYInt
      (Filter.Eventually.of_forall hYNonneg)]
    exact hmoment'
  have hvariance : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) := by
    exact_mod_cast hnum.variance_nonneg
  exact ⟨hYInt, (ENNReal.ofReal_le_ofReal_iff hvariance).mp hreal⟩

theorem nativeHeatRefined_rareQuadratic_integral_le_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ)) :
    Integrable (nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        2 * (nativeHeatEps : ℝ) * ((nativeHeatGenVariance ns) : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m
  have hRNonneg := nativeHeatRefinedRare_nonneg_Gen ns M h hM hg m hpast
  have hmoment := hRare 1 le_rfl (by norm_num)
  have hmeasR : Measurable R := nativeHeatRefinedRare_measurable_Gen ns M h hM hg m hpast
  have hmoment2 : ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ∂μ ≤
      ENNReal.ofReal (2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ)))) := by
    simpa [μ, mul_assoc] using hmoment
  have hmoment' : ∫⁻ ω, ‖R ω‖ₑ ∂μ ≤ ENNReal.ofReal
      (2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ)))) := by
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
              ((nativeHeatGenVariance ns) : ℝ)))) := hmoment'
      _ < ∞ := ENNReal.ofReal_lt_top
  have hRInt : Integrable R μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmeasR.aestronglyMeasurable (Filter.Eventually.of_forall hRNonneg)).mp hfinite
  have hreal : ENNReal.ofReal (∫ ω, R ω ∂μ) ≤ ENNReal.ofReal
      (2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ)))) := by
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
              ((nativeHeatGenVariance ns) : ℝ)))) := hmoment'
  have hcapNonneg : 0 ≤ 2 * ((inverseBankReserve .localInverse : ℝ) *
      (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
        ((nativeHeatGenVariance ns) : ℝ))) := by
    have hgmNonneg : 0 ≤ ((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) :=
      nativeHeatInitialGM_nonneg 1 (by norm_num) (by norm_num)
    have hreserve : 0 ≤ (inverseBankReserve .localInverse : ℝ) := by
      norm_num [inverseBankReserve]
    have hv : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) := by
      exact_mod_cast hnum.variance_nonneg
    exact mul_nonneg (by norm_num) (mul_nonneg hreserve (mul_nonneg hgmNonneg hv))
  have hRbound : ∫ ω, R ω ∂μ ≤
      2 * ((inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) :=
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
  have hvariance : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) := by
    exact_mod_cast hnum.variance_nonneg
  have hcap : 2 * ((inverseBankReserve .localInverse : ℝ) *
      (((nativeHeatParametersData.gm.getD 1 0 : ℚ) : ℝ) *
        ((nativeHeatGenVariance ns) : ℝ))) ≤
      2 * (nativeHeatEps : ℝ) * ((nativeHeatGenVariance ns) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hreserveGMReal hvariance
    nlinarith [hmul]
  exact ⟨hRInt, hRbound.trans hcap⟩

theorem nativeHeatRefined_initialFirstMoment_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ)) :
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeUp
        (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
          (nativeHeatGenVariance ns)) : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let old := nativeHeatRefinedOldAverage M m
  let Y := nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m
  let C := nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m
  let R := nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m
  let F : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    old ω + 2 * (nativeHeatB : ℝ) * Y ω + C ω + R ω
  have hOld : Integrable old μ ∧ ∫ ω, old ω ∂μ ≤ (nativeQstar : ℝ) := by
    obtain ⟨hint, hmeanEq, hmeanLe⟩ :=
      nativeHeatRefinedOldAverage_mean M h hM hg m hpast
    exact ⟨hint, hmeanEq ▸ hmeanLe⟩
  have hY := nativeHeatRefined_centerQuadratic_integral_le_Gen ns hnum M m hGauss
  have hR := nativeHeatRefined_rareQuadratic_integral_le_Gen ns hnum M h hM hg m hpast hRare
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
      2 * (nativeHeatB : ℝ) * ((nativeHeatGenVariance ns) : ℝ) :=
    mul_le_mul_of_nonneg_left hY.2 hBnonneg
  have hFbound : ∫ ω, F ω ∂μ ≤
      (nativeQstar : ℝ) +
        2 * ((nativeHeatB : ℝ) + (nativeHeatEps : ℝ)) *
          ((nativeHeatGenVariance ns) : ℝ) := by
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
        ((nativeQstar : ℝ) +
          2 * ((nativeHeatB : ℝ) + (nativeHeatEps : ℝ)) *
            ((nativeHeatGenVariance ns) : ℝ)) := ENNReal.ofReal_le_ofReal hFbound
    _ ≤ ENNReal.ofReal (nativeUp
        (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
          (nativeHeatGenVariance ns)) : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        exact_mod_cast nativeUp_ge
          (nativeQstar + 2 * (nativeHeatB + nativeHeatEps) *
            (nativeHeatGenVariance ns))

theorem nativeHeatRefined_initialMoment_ge_two_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
            (k : ℝ))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (nativeHeatInitialAt nativeHeatParametersData
          (nativeHeatGenQm ns) (nativeHeatGenVariance ns) k : ℝ) := by
  classical
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
  have hYint := (nativeHeatRefined_centerQuadratic_integral_le_Gen ns hnum M m hGauss).1
  have hCint := (nativeHeatRefinedShearCross_integrable_zero_Gen ns M h hM hg m hpast hYint).1
  have hAes : AEStronglyMeasurable A μ := hAmeas.aestronglyMeasurable
  have hCes : AEStronglyMeasurable C μ := hCint.aestronglyMeasurable
  have hRes : AEStronglyMeasurable R μ :=
    (nativeHeatRefinedRare_measurable_Gen ns M h hM hg m hpast).aestronglyMeasurable
  have hAabsMeas : AEStronglyMeasurable Aabs μ := hAes.norm
  have hCabsMeas : AEStronglyMeasurable Cabs μ := hCes.norm
  have hRabsMeas : AEStronglyMeasurable Rabs μ := hRes.norm
  have hA_lp := nativeHeatRefined_initialBaseLp_Gen ns hnum
    M h hM hg m hpast hGauss k hk2 hk20
  have hC_lp := nativeHeatRefined_initialCrossLp_Gen ns hnum M h hM m hCross k hk2 hk20
  have hR_lp := nativeHeatRefined_initialRareLp_Gen ns hnum M h hM m hRare k hk2 hk20
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
    (ENNReal.ofReal (baseRootQ : ℝ)) (ENNReal.ofReal (crossQ : ℝ))
    (ENNReal.ofReal (rareQ : ℝ))
    hkpos hk1R hAabsMeas hCabsMeas hRabsMeas
    (fun ω => norm_nonneg _) (fun ω => norm_nonneg _) (fun ω => norm_nonneg _)
    hOmono hA_lp hC_lp hR_lp
  have hsumCaps :
      ENNReal.ofReal (baseRootQ : ℝ) + ENNReal.ofReal (crossQ : ℝ) +
        ENNReal.ofReal (rareQ : ℝ) = ENNReal.ofReal (totalQ : ℝ) := by
    calc
      _ = ENNReal.ofReal ((baseRootQ : ℝ) + (crossQ : ℝ)) +
          ENNReal.ofReal (rareQ : ℝ) := by
        rw [ENNReal.ofReal_add hbaseRootNonneg hcrossRootNonneg]
      _ = ENNReal.ofReal
          (((baseRootQ : ℝ) + (crossQ : ℝ)) + (rareQ : ℝ)) := by
        rw [ENNReal.ofReal_add (add_nonneg hbaseRootNonneg hcrossRootNonneg)
          hrareRootNonneg]
      _ = ENNReal.ofReal (totalQ : ℝ) := by simp [totalQ]
  have htotalLp : eLpNorm' (nativeHeatRefinedObservableGen ns M m)
      (k : ℝ) μ ≤ ENNReal.ofReal (totalQ : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (baseRootQ : ℝ) + ENNReal.ofReal (crossQ : ℝ) +
          ENNReal.ofReal (rareQ : ℝ) := hLp
      _ = ENNReal.ofReal (totalQ : ℝ) := hsumCaps
  have hrow : nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
      (nativeHeatGenVariance ns) k = nativeUp (totalQ ^ k) := by
    have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp [nativeHeatInitialAt, hk0, hk1, baseQ, baseSumQ, baseTerm, baseRootQ,
      innerRootQ, crossRawQ, crossQ, rareRawQ, rareQ, totalQ, qh]
  calc
    _ = (eLpNorm' (nativeHeatRefinedObservableGen ns M m) (k : ℝ) μ) ^ (k : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
    _ ≤ (ENNReal.ofReal (totalQ : ℝ)) ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow htotalLp (by positivity)
    _ = ENNReal.ofReal ((totalQ : ℝ) ^ k) := by
      rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow htotalNonneg]
    _ ≤ ENNReal.ofReal (nativeUp (totalQ ^ k) : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast nativeUp_ge (totalQ ^ k)
    _ = ENNReal.ofReal
        (nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
          (nativeHeatGenVariance ns) k : ℝ) := by rw [hrow]

/-- Every refined initial row, from the three component rows. -/
theorem nativeHeatRefined_initialMoment_of_providers_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
            (k : ℝ))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ))
    (k : ℕ) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatRefinedObservableGen ns M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (nativeHeatInitialAt nativeHeatParametersData
          (nativeHeatGenQm ns) (nativeHeatGenVariance ns) k : ℝ) := by
  by_cases hk0 : k = 0
  · subst k
    letI : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
      (Cutoff.cutoffSampleLaw M).property
    simp [nativeHeatInitialAt]
  · by_cases hk1 : k = 1
    · subst k
      simpa [nativeHeatInitialAt] using
        nativeHeatRefined_initialFirstMoment_Gen ns hnum M h hM hg m hpast hGauss hRare
    · have hk2 : 2 ≤ k := by omega
      exact nativeHeatRefined_initialMoment_ge_two_Gen ns hnum
        M h hM hg m hpast hGauss hCross hRare k hk2 hk20

/-- At backward time zero the source-normalized carrier moment is the
integral of the power of the refined start observable. -/
theorem nativeHeatRefined_sourceMoment_zero_eq_integral_Gen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (k : ℕ) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k (nativeHeatTheta : ℝ) 0 =
      ∫ ω, (nativeHeatRefinedObservableGen ns M m ω) ^ k
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hθ : (0 : ℝ) < (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  rw [nativeHeatQ3RefinedCarrierSourceMoment_zero_eq_actualBandAverageGen ns M m Ffam k (nativeHeatTheta : ℝ) hθ]
  unfold bandModelAverage
  apply integral_congr_ae
  filter_upwards [] with ω
  unfold nativeHeatQ3RefinedCarrierPowerTest childPower nativeHeatRefinedObservableGen
  congr 2
  simp only [ContinuousLinearMap.comp_apply, map_smul]
  congr 1
  ext i x
  simp [childConstantMap, nativeHeatQ3RefinedCarrierSourceFreshRawGen]

/-- Conditional refined initial row at the carrier. -/
theorem nativeHeatQ3RefinedCarrierSourceInitialMoment_le_009_of_providers_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hGauss : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      ∫⁻ ω, ENNReal.ofReal
        (nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω ^ j)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((nativeHeatGenQm ns).getD j 0 : ℚ) : ℝ))
    (hCross : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          ((nativeHeatGenQm ns).getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
            (k : ℝ))
    (hRare : ∀ k : ℕ, 1 ≤ k → k ≤ 20 →
      ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ))
    (k : ℕ) (hk20 : k ≤ 20) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k (nativeHeatTheta : ℝ) 0 ≤
      ((nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
        (nativeHeatGenVariance ns) k : ℚ) : ℝ) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  rw [nativeHeatRefined_sourceMoment_zero_eq_integral_Gen]
  have hrow := nativeHeatRefined_initialMoment_of_providers_Gen ns hnum M h hM hg m hpast
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
  have hcap : (0 : ℝ) ≤ ((nativeHeatInitialAt nativeHeatParametersData (nativeHeatGenQm ns)
      (nativeHeatGenVariance ns) k : ℚ) : ℝ) := by exact_mod_cast hcapQ
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
