module

public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Cold.NativeGraphTraceAverage
public import ASDExplicitGamma.Cold.SquareCellMean
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Native.HeatInitialCrossTypeTwo

/-! Product-law and moment interfaces for the old/fresh initial heat split. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3.Provider.BadEvents
open scoped ENNReal BigOperators

noncomputable section

set_option linter.constructorNameAsVariable false

/-- Binomial moments of a sum of independent nonnegative variables are
controlled by the product of their separate moment rows. -/
theorem nativeHeat_independent_nonneg_add_moment_of_caps
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) (hXnonneg : ∀ ω, 0 ≤ X ω)
    (hYnonneg : ∀ ω, 0 ≤ Y ω) (c : ℝ) (hc : 0 ≤ c) (k : ℕ)
    (A B : ℕ → ℝ) (hA : ∀ n ≤ k, 0 ≤ A n) (hB : ∀ n ≤ k, 0 ≤ B n)
    (hXmom : ∀ n ≤ k,
      ∫⁻ ω, ‖X ω‖ₑ ^ (n : ℝ) ∂μ ≤ ENNReal.ofReal (A n))
    (hYmom : ∀ n ≤ k,
      ∫⁻ ω, ‖Y ω‖ₑ ^ (n : ℝ) ∂μ ≤ ENNReal.ofReal (B n)) :
    ∫⁻ ω, ‖X ω + c * Y ω‖ₑ ^ (k : ℝ) ∂μ ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) * A (k - j) * c ^ j * B j) := by
  classical
  let Xpow : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (X ω ^ n)
  let Ypow : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Y ω ^ n)
  let Zpow : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal ((c * Y ω) ^ n)
  let term : ℕ → Ω → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal (Nat.choose k j : ℝ) * (Xpow (k - j) ω * Zpow j ω)
  have hXpowMeas (n : ℕ) : Measurable (Xpow n) := by
    exact ENNReal.measurable_ofReal.comp (hX.pow_const n)
  have hYpowMeas (n : ℕ) : Measurable (Ypow n) := by
    exact ENNReal.measurable_ofReal.comp (hY.pow_const n)
  have hZpowMeas (n : ℕ) : Measurable (Zpow n) := by
    exact ENNReal.measurable_ofReal.comp ((measurable_const.mul hY).pow_const n)
  have hIndepScaledPow (j : ℕ) : IndepFun (Xpow (k - j)) (Zpow j) μ := by
    change (fun ω => ENNReal.ofReal (X ω ^ (k - j))) ⟂ᵢ[μ]
      (fun ω => ENNReal.ofReal ((c * Y ω) ^ j))
    exact hXY.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const (k - j)))
      (ENNReal.measurable_ofReal.comp
        ((measurable_const.mul measurable_id).pow_const j))
  have hXmoment (n : ℕ) (hn : n ≤ k) :
      ∫⁻ ω, Xpow n ω ∂μ ≤ ENNReal.ofReal (A n) := by
    have hpoint (ω : Ω) : Xpow n ω = ‖X ω‖ₑ ^ (n : ℝ) := by
      dsimp [Xpow]
      rw [ENNReal.ofReal_pow (hXnonneg ω), Real.enorm_eq_ofReal (hXnonneg ω)]
      simp
    rw [lintegral_congr hpoint]
    exact hXmom n hn
  have hYmoment (n : ℕ) (hn : n ≤ k) :
      ∫⁻ ω, Ypow n ω ∂μ ≤ ENNReal.ofReal (B n) := by
    have hpoint (ω : Ω) : Ypow n ω = ‖Y ω‖ₑ ^ (n : ℝ) := by
      dsimp [Ypow]
      rw [ENNReal.ofReal_pow (hYnonneg ω), Real.enorm_eq_ofReal (hYnonneg ω)]
      simp
    rw [lintegral_congr hpoint]
    exact hYmom n hn
  have hYscaled (j : ℕ) (hj : j ≤ k) :
      ∫⁻ ω, ENNReal.ofReal ((c * Y ω) ^ j) ∂μ ≤
        ENNReal.ofReal (c ^ j * B j) := by
    have hscale :
        ∫⁻ ω, ENNReal.ofReal ((c * Y ω) ^ j) ∂μ =
          ENNReal.ofReal (c ^ j) * ∫⁻ ω, Ypow j ω ∂μ := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (c ^ j) * Ypow j ω ∂μ := by
          apply lintegral_congr
          intro ω
          dsimp [Ypow]
          rw [mul_pow, ← ENNReal.ofReal_mul (pow_nonneg hc j)]
        _ = _ := lintegral_const_mul _ (hYpowMeas j)
    have hright := mul_le_mul_of_nonneg_left (hYmoment j hj)
      (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (c ^ j))
    calc
      _ = ENNReal.ofReal (c ^ j) * ∫⁻ ω, Ypow j ω ∂μ := hscale
      _ ≤ ENNReal.ofReal (c ^ j) * ENNReal.ofReal (B j) := hright
      _ = ENNReal.ofReal (c ^ j * B j) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hc j)]
  have hZmoment (j : ℕ) (hj : j ≤ k) :
      ∫⁻ ω, Zpow j ω ∂μ ≤ ENNReal.ofReal (c ^ j * B j) := by
    simpa [Zpow] using hYscaled j hj
  have htermFactor (j : ℕ) :
      ∫⁻ ω, term j ω ∂μ =
        ENNReal.ofReal (Nat.choose k j : ℝ) *
          ((∫⁻ ω, Xpow (k - j) ω ∂μ) * ∫⁻ ω, Zpow j ω ∂μ) := by
    calc
      ∫⁻ ω, term j ω ∂μ =
          ENNReal.ofReal (Nat.choose k j : ℝ) *
            ∫⁻ ω, Xpow (k - j) ω * Zpow j ω ∂μ := by
        dsimp [term]
        exact lintegral_const_mul _ ((hXpowMeas (k - j)).mul (hZpowMeas j))
      _ = _ := congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal (Nat.choose k j : ℝ) * z)
        (lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
          (f := Xpow (k - j)) (g := Zpow j)
          (hXpowMeas (k - j)) (hZpowMeas j) (hIndepScaledPow j))
  have htermBound (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      ∫⁻ ω, term j ω ∂μ ≤
        ENNReal.ofReal ((Nat.choose k j : ℝ) * A (k - j) * c ^ j * B j) := by
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hn : k - j ≤ k := Nat.le_trans (Nat.sub_le _ _) le_rfl
    have hfac := htermFactor j
    have hmul := mul_le_mul (hXmoment (k - j) hn) (hZmoment j hjk)
      (by positivity : (0 : ℝ≥0∞) ≤ ∫⁻ ω, Zpow j ω ∂μ)
      (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (A (k - j)))
    calc
      _ = ENNReal.ofReal (Nat.choose k j : ℝ) *
          ((∫⁻ ω, Xpow (k - j) ω ∂μ) * ∫⁻ ω, Zpow j ω ∂μ) := hfac
      _ ≤ ENNReal.ofReal (Nat.choose k j : ℝ) *
          (ENNReal.ofReal (A (k - j)) * ENNReal.ofReal (c ^ j * B j)) := by
            exact mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = ENNReal.ofReal ((Nat.choose k j : ℝ) * A (k - j) * c ^ j * B j) := by
            rw [← ENNReal.ofReal_mul (hA (k - j) hn),
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1
            ring
  have hbinom (ω : Ω) :
      ‖X ω + c * Y ω‖ₑ ^ (k : ℝ) = ∑ j ∈ Finset.range (k + 1), term j ω := by
    have hnonneg : 0 ≤ X ω + c * Y ω :=
      add_nonneg (hXnonneg ω) (mul_nonneg hc (hYnonneg ω))
    have hsum :
        (X ω + c * Y ω) ^ k =
          ∑ j ∈ Finset.range (k + 1),
            (Nat.choose k j : ℝ) * X ω ^ (k - j) * (c * Y ω) ^ j := by
      let F : ℕ → ℝ := fun i => X ω ^ i * (c * Y ω) ^ (k - i) * (Nat.choose k i : ℝ)
      calc
        _ = ∑ j ∈ Finset.range (k + 1), F j := by
          rw [add_pow]
        _ = ∑ j ∈ Finset.range (k + 1), F (k - j) := by
          simpa only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] using
            (Finset.sum_range_reflect F (k + 1)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          dsimp [F]
          rw [Nat.sub_sub_self hjk, Nat.choose_symm hjk]
          ring
    calc
      _ = ENNReal.ofReal ((X ω + c * Y ω) ^ k) := by
        rw [Real.enorm_eq_ofReal hnonneg, ENNReal.rpow_natCast,
          ← ENNReal.ofReal_pow hnonneg]
      _ = ∑ j ∈ Finset.range (k + 1),
            ENNReal.ofReal ((Nat.choose k j : ℝ) * X ω ^ (k - j) *
              (c * Y ω) ^ j) := by
        rw [hsum, ENNReal.ofReal_sum_of_nonneg fun j hj =>
          mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hXnonneg ω) _))
            (pow_nonneg (mul_nonneg hc (hYnonneg ω)) _)]
      _ = ∑ j ∈ Finset.range (k + 1), term j ω := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [term, Xpow, Zpow]
        rw [ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hXnonneg ω) _)),
          ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp only [mul_assoc]
  have htermMeas (j : ℕ) : Measurable (term j) := by
    dsimp [term]
    exact measurable_const.mul ((hXpowMeas (k - j)).mul (hZpowMeas j))
  calc
    _ = ∫⁻ ω, ∑ j ∈ Finset.range (k + 1), term j ω ∂μ :=
      lintegral_congr hbinom
    _ = ∑ j ∈ Finset.range (k + 1), ∫⁻ ω, term j ω ∂μ := by
      exact lintegral_finsetSum _ (fun j _ =>
        (htermMeas j))
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        ENNReal.ofReal ((Nat.choose k j : ℝ) * A (k - j) * c ^ j * B j) :=
      Finset.sum_le_sum fun j hj => htermBound j hj
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) * A (k - j) * c ^ j * B j) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg fun j hj => by
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hkminus : k - j ≤ k := Nat.le_trans (Nat.sub_le _ _) le_rfl
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA _ hkminus))
            (pow_nonneg hc _)) (hB _ hjk)

end

end ASDExplicitGamma.Native
