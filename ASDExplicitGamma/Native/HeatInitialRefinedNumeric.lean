module

public import ASDExplicitGamma.Native.HeatInitialCrossRow
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Gaussian.NormalEvenMoments
public import ASDExplicitGamma.Native.HeatInitialCrossTypeTwo
public import ASDExplicitGamma.Native.HeatInitialProduct
public import ASDExplicitGamma.Numerics.Native.Heat009Initial

/-! Exact 009 numeric bindings for the refined initial row: nonnegativity of the
configured coefficients, the base-row root certificates, and the Lp
bookkeeping shared by the refined assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators

noncomputable section

theorem nativeHeat009_initialBaseRootValid
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    nativeRootValid
      (nativeUp (((List.range (k + 1)).map fun j =>
        (Nat.choose k j : ℚ) *
          nativeInitialMeanMoment nativeHeatParametersData (k - j) *
          (2 * nativeHeatB) ^ j * nativeHeat009Qm.getD j 0).sum)) k = true := by
  interval_cases k <;> decide +kernel

theorem nativeHeatInitialGM_nonneg (k : ℕ)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    0 ≤ ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) := by
  interval_cases k <;> first
    | exact_mod_cast nativeHeatGM01_powers.1
    | exact_mod_cast nativeHeatGM02_powers.1
    | exact_mod_cast nativeHeatGM03_powers.1
    | exact_mod_cast nativeHeatGM04_powers.1
    | exact_mod_cast nativeHeatGM05_powers.1
    | exact_mod_cast nativeHeatGM06_powers.1
    | exact_mod_cast nativeHeatGM07_powers.1
    | exact_mod_cast nativeHeatGM08_powers.1
    | exact_mod_cast nativeHeatGM09_powers.1
    | exact_mod_cast nativeHeatGM10_powers.1
    | exact_mod_cast nativeHeatGM11_powers.1
    | exact_mod_cast nativeHeatGM12_powers.1
    | exact_mod_cast nativeHeatGM13_powers.1
    | exact_mod_cast nativeHeatGM14_powers.1
    | exact_mod_cast nativeHeatGM15_powers.1
    | exact_mod_cast nativeHeatGM16_powers.1
    | exact_mod_cast nativeHeatGM17_powers.1
    | exact_mod_cast nativeHeatGM18_powers.1
    | exact_mod_cast nativeHeatGM19_powers.1
    | exact_mod_cast nativeHeatGM20_powers.1

theorem nativeHeatCrossReal_nonneg (k : ℕ) :
    0 ≤ nativeHeatCrossReal nativeHeatParametersData k := by
  have hp : 0 ≤ nativeHeatParametersData.hp := by
    norm_num [nativeHeatParametersData]
  have hq : 0 < nativeQstar := by norm_num [nativeQstar]
  have hratio : 0 ≤ (nativeHeatParametersData.hp / nativeQstar : ℚ) :=
    div_nonneg hp hq.le
  have hHn : 0 ≤ nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) := by
    unfold nativeHeatHnReal
    positivity
  have hB : 0 ≤ (nativeHeatB : ℝ) := by
    norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
  have hEps : 0 ≤ (nativeHeatEps : ℝ) := by
    norm_num [nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeEps]
  unfold nativeHeatCrossReal
  positivity

theorem nativeHeatCrossData_nonneg (k : ℕ)
    (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    0 ≤ ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) := by
  have hreal := nativeHeatCrossReal_nonneg k
  have hbound : nativeHeatCrossReal nativeHeatParametersData k ≤
      ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) := by
    interval_cases k <;> first
      | omega
      | exact nativeHeatCross02_bound
      | exact nativeHeatCross03_bound
      | exact nativeHeatCross04_bound
      | exact nativeHeatCross05_bound
      | exact nativeHeatCross06_bound
      | exact nativeHeatCross07_bound
      | exact nativeHeatCross08_bound
      | exact nativeHeatCross09_bound
      | exact nativeHeatCross10_bound
      | exact nativeHeatCross11_bound
      | exact nativeHeatCross12_bound
      | exact nativeHeatCross13_bound
      | exact nativeHeatCross14_bound
      | exact nativeHeatCross15_bound
      | exact nativeHeatCross16_bound
      | exact nativeHeatCross17_bound
      | exact nativeHeatCross18_bound
      | exact nativeHeatCross19_bound
      | exact nativeHeatCross20_bound
  exact hreal.trans hbound

theorem nativeHeatInitialLp_of_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ)
    (p cap : ℝ) (hp : 0 < p)
    (hmoment : ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ ≤ (ENNReal.ofReal cap) ^ p) :
    eLpNorm' f p μ ≤ ENNReal.ofReal cap := by
  have hpow : (eLpNorm' f p μ) ^ p ≤ (ENNReal.ofReal cap) ^ p := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
    exact hmoment
  exact (ENNReal.rpow_le_rpow_iff hp).mp hpow

theorem nativeHeatInitial_listSum_eq_finsetSum
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, ih, Finset.sum_range_succ]

theorem nativeHeatInitialLp_three_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (O A C R : Ω → ℝ) (p : ℝ)
    (capA capC capR : ℝ≥0∞)
    (hp : 0 < p) (hp1 : 1 ≤ p)
    (hAes : AEStronglyMeasurable A μ) (hCes : AEStronglyMeasurable C μ)
    (hRes : AEStronglyMeasurable R μ)
    (hAnonneg : ∀ ω, 0 ≤ A ω) (hCnonneg : ∀ ω, 0 ≤ C ω)
    (hRnonneg : ∀ ω, 0 ≤ R ω)
    (hmono : ∀ᵐ ω ∂μ, ‖O ω‖ ≤ A ω + C ω + R ω)
    (hAlp : eLpNorm' A p μ ≤ capA) (hClp : eLpNorm' C p μ ≤ capC)
    (hRlp : eLpNorm' R p μ ≤ capR) :
    eLpNorm' O p μ ≤ capA + capC + capR := by
  let F : Ω → ℝ := fun ω => A ω + C ω + R ω
  have hAC : eLpNorm' (fun ω => A ω + C ω) p μ ≤
      eLpNorm' A p μ + eLpNorm' C p μ :=
    eLpNorm'_add_le hAes hCes hp1
  have hFlp : eLpNorm' F p μ ≤
      (eLpNorm' A p μ + eLpNorm' C p μ) + eLpNorm' R p μ := by
    calc
      _ = eLpNorm' (fun ω => (A ω + C ω) + R ω) p μ := rfl
      _ ≤ eLpNorm' (fun ω => A ω + C ω) p μ + eLpNorm' R p μ :=
        eLpNorm'_add_le (hAes.add hCes) hRes hp1
      _ ≤ _ := by gcongr
  have hOmono : ∀ᵐ ω ∂μ, ‖O ω‖ ≤ ‖F ω‖ := by
    filter_upwards [hmono] with ω hω
    have hFnonneg : 0 ≤ F ω := by
      dsimp [F]
      exact add_nonneg (add_nonneg (hAnonneg ω) (hCnonneg ω)) (hRnonneg ω)
    simpa [F, Real.norm_of_nonneg hFnonneg] using hω
  calc
    eLpNorm' O p μ ≤ eLpNorm' F p μ := eLpNorm'_mono_ae (le_of_lt hp) hOmono
    _ ≤ (eLpNorm' A p μ + eLpNorm' C p μ) + eLpNorm' R p μ := hFlp
    _ ≤ (capA + capC) + capR := by
      exact add_le_add (add_le_add hAlp hClp) hRlp

theorem nativeHeatRootUp_nonneg (x : ℚ) (n : ℕ) :
    0 ≤ nativeRootUp x n := by
  unfold nativeRootUp
  split_ifs
  · norm_num
  · apply div_nonneg
    · positivity
    · positivity

theorem nativeHeatPowUp_nonneg (x q : ℚ) (hx : 0 ≤ x) :
    0 ≤ nativePowUp x q := by
  unfold nativePowUp
  split_ifs
  · exact pow_nonneg hx _
  · exact nativeHeatRootUp_nonneg _ _

theorem nativeInitialMeanMoment_nonneg (n : ℕ) :
    0 ≤ nativeInitialMeanMoment nativeHeatParametersData n := by
  by_cases hn0 : n = 0
  · simp [nativeInitialMeanMoment, hn0]
  have hqstar : 0 < nativeQstar := by norm_num [nativeQstar]
  have hhp : 0 ≤ nativeHeatParametersData.hp := by
    norm_num [nativeHeatParametersData]
  have hbase : 0 ≤
      (nativeQstar + (50 / 3^9) * nativeHeatParametersData.hp) / nativeQstar := by
    apply div_nonneg
    · exact add_nonneg hqstar.le (mul_nonneg (by norm_num) hhp)
    · exact hqstar.le
  have hpow := nativeHeatPowUp_nonneg
    ((nativeQstar + (50 / 3^9) * nativeHeatParametersData.hp) / nativeQstar)
    ((20 * (n - 1 : ℕ) : ℕ) / (19 : ℚ)) hbase
  have hproduct : 0 ≤ nativeQstar^n * nativePowUp
      ((nativeQstar + (50 / 3^9) * nativeHeatParametersData.hp) / nativeQstar)
      ((20 * (n - 1 : ℕ) : ℕ) / (19 : ℚ)) :=
    mul_nonneg (pow_nonneg (by positivity : (0 : ℚ) ≤ nativeQstar) n) hpow
  have hrounded := nativeUp_ge (nativeQstar^n * nativePowUp
    ((nativeQstar + (50 / 3^9) * nativeHeatParametersData.hp) / nativeQstar)
    ((20 * (n - 1 : ℕ) : ℕ) / (19 : ℚ)))
  have hresult : 0 ≤ nativeUp (nativeQstar^n * nativePowUp
      ((nativeQstar + (50 / 3^9) * nativeHeatParametersData.hp) / nativeQstar)
      ((20 * (n - 1 : ℕ) : ℕ) / (19 : ℚ))) := hproduct.trans hrounded
  simpa [nativeInitialMeanMoment, hn0] using hresult

theorem nativeHeat009Qm_nonneg (j : ℕ) (hj20 : j ≤ 20) :
    0 ≤ nativeHeat009Qm.getD j 0 := by
  interval_cases j <;> norm_num [nativeHeat009Qm]

end

end ASDExplicitGamma.Native
