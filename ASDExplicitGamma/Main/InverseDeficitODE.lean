module

public import ASDExplicitGamma.Main.PanelComparison
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.InverseLowerAlgebra
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Integrating-factor estimate for the absolute inverse-deficit branch. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Set

/-- The source cubic expansion for the absolute inverse-deficit branch. The
global inverse bank supplies `B ≤ beta + R`; the trace defect obeys `d ≤ 2B`.
This pointwise inequality is the deterministic input before the three
remainder moments are integrated. -/
theorem main_inverse_deficit_cubic_integrand_bound
    {Ω : Type*} (beta : ℝ) (B d R : Ω → ℝ)
    (hbeta : 0 ≤ beta) :
    ∀ ω, 0 ≤ R ω → B ω ≤ beta + R ω →
      (0 ≤ d ω ∧ d ω ≤ 2 * B ω) →
        B ω ^ 2 * d ω ≤
          beta ^ 2 * d ω + 2 * (2 * beta ^ 2 * R ω + 3 * beta * R ω ^ 2 + R ω ^ 3) := by
  intro ω hR hB hd
  have hB0 : 0 ≤ B ω := by linarith [hd.1, hd.2]
  have hsum0 : 0 ≤ beta + R ω := add_nonneg hbeta hR
  have hsq : B ω ^ 2 ≤ (beta + R ω) ^ 2 := by
    nlinarith [hB, hB0, hsum0]
  have hdbound : d ω ≤ 2 * (beta + R ω) := by
    linarith [hd.2, hB]
  calc
    B ω ^ 2 * d ω ≤ (beta + R ω) ^ 2 * d ω :=
      mul_le_mul_of_nonneg_right hsq hd.1
    _ = beta ^ 2 * d ω + (2 * beta * R ω + R ω ^ 2) * d ω := by ring
    _ ≤ beta ^ 2 * d ω +
        (2 * beta * R ω + R ω ^ 2) * (2 * (beta + R ω)) := by
      have hcoef : 0 ≤ 2 * beta * R ω + R ω ^ 2 :=
        add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hbeta) hR)
          (sq_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hdbound hcoef
      nlinarith
    _ = beta ^ 2 * d ω +
        2 * (2 * beta ^ 2 * R ω + 3 * beta * R ω ^ 2 + R ω ^ 3) := by ring

/-- Integrating the pointwise inverse-deficit expansion charges only the
first three remainder moments. The integrability conditions are analytic
side conditions for the actual bank profiles, not estimates or conclusions
being assumed. -/
theorem main_inverse_deficit_cubic_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (beta : ℝ) (B d R : Ω → ℝ)
    (hbeta : 0 ≤ beta) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hB : ∀ᵐ ω ∂μ, B ω ≤ beta + R ω)
    (hdBounds : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * B ω)
    (hLeft : Integrable (fun ω => B ω ^ 2 * d ω) μ)
    (hdInt : Integrable d μ) (hR : Integrable R μ)
    (hR2 : Integrable (fun ω => R ω ^ 2) μ)
    (hR3 : Integrable (fun ω => R ω ^ 3) μ) :
    ∫ ω, B ω ^ 2 * d ω ∂μ ≤
      beta ^ 2 * (∫ ω, d ω ∂μ) +
        2 * (2 * beta ^ 2 * (∫ ω, R ω ∂μ) +
          3 * beta * (∫ ω, R ω ^ 2 ∂μ) + ∫ ω, R ω ^ 3 ∂μ) := by
  let P1 : Ω → ℝ := fun ω => 2 * beta ^ 2 * R ω
  let P2 : Ω → ℝ := fun ω => 3 * beta * R ω ^ 2
  let P3 : Ω → ℝ := fun ω => R ω ^ 3
  let P12 : Ω → ℝ := P1 + P2
  let P : Ω → ℝ := P12 + P3
  let D0 : Ω → ℝ := fun ω => beta ^ 2 * d ω
  let D1 : Ω → ℝ := fun ω => 2 * P ω
  have hCubic : ∀ᵐ ω ∂μ,
      B ω ^ 2 * d ω ≤
        beta ^ 2 * d ω + 2 * (2 * beta ^ 2 * R ω + 3 * beta * R ω ^ 2 + R ω ^ 3) :=
    by
      filter_upwards [hR0,hB,hdBounds] with ω hRω hBω hdω
      exact main_inverse_deficit_cubic_integrand_bound beta B d R
        hbeta ω hRω hBω hdω
  have hP12 : Integrable P12 μ := by
    exact (hR.const_mul (2 * beta ^ 2)).add (hR2.const_mul (3 * beta))
  have hP : Integrable P μ := hP12.add hR3
  have hRight : Integrable (D0 + D1) μ := by
    exact (hdInt.const_mul (beta ^ 2)).add (hP.const_mul 2)
  have hPoint : ∀ᵐ ω ∂μ, B ω ^ 2 * d ω ≤ (D0 + D1) ω := by
    filter_upwards [hCubic] with ω hω
    simpa only [D0, D1, P, P12, P1, P2, P3, Pi.add_apply] using hω
  have hmono := integral_mono_ae hLeft hRight hPoint
  have hPint : (∫ ω, P ω ∂μ) =
      2 * beta ^ 2 * (∫ ω, R ω ∂μ) +
        3 * beta * (∫ ω, R ω ^ 2 ∂μ) + ∫ ω, R ω ^ 3 ∂μ := by
    calc
      _ = (∫ ω, P12 ω ∂μ) + (∫ ω, P3 ω ∂μ) := integral_add hP12 hR3
      _ = (∫ ω, P1 ω ∂μ) + (∫ ω, P2 ω ∂μ) +
          (∫ ω, P3 ω ∂μ) := by rw [show (∫ ω, P12 ω ∂μ) =
            (∫ ω, P1 ω ∂μ) + (∫ ω, P2 ω ∂μ) from integral_add
              (hR.const_mul (2 * beta ^ 2)) (hR2.const_mul (3 * beta))]
      _ = _ := by
        dsimp [P1, P2, P3]
        rw [integral_const_mul, integral_const_mul]
  have hRightInt :
      (∫ ω, (D0 + D1) ω ∂μ) =
        beta ^ 2 * (∫ ω, d ω ∂μ) +
          2 * (2 * beta ^ 2 * (∫ ω, R ω ∂μ) +
            3 * beta * (∫ ω, R ω ^ 2 ∂μ) + ∫ ω, R ω ^ 3 ∂μ) := by
    calc
      _ = (∫ ω, D0 ω ∂μ) + (∫ ω, D1 ω ∂μ) := integral_add
        (hdInt.const_mul (beta ^ 2)) (hP.const_mul 2)
      _ = _ := by
        dsimp [D0, D1]
        rw [integral_const_mul, integral_const_mul, hPint]
  simpa only [D0, D1, P, P12, P1, P2, P3, Pi.add_apply] using
    hmono.trans_eq hRightInt

/-- A nonnegative remainder with its actual probability-law L128 cap has
the three lower moments charged by the inverse-deficit cubic expansion. -/
theorem main_inverse_deficit_remainder_moment_le_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (epsilon : ℝ) (k : ℕ)
    (hk : 0 < k) (hk128 : k ≤ 128)
    (hR : MemLp R 128 μ) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hcap : lpNorm R 128 μ ≤ epsilon) :
    ∫ ω, R ω ^ k ∂μ ≤ epsilon ^ k := by
  let p : ENNReal := ENNReal.ofReal (k : ℝ)
  have hpReal : p.toReal = (k : ℝ) := by
    simp [p]
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hp0 : p ≠ 0 := by
    simp [p, Nat.cast_ne_zero.mpr hk.ne']
  have hptop : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp128 : p ≤ (128 : ENNReal) := by
    change ENNReal.ofReal (k : ℝ) ≤ (128 : ENNReal)
    calc
      ENNReal.ofReal (k : ℝ) ≤ ENNReal.ofReal (128 : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast hk128)
      _ = (128 : ENNReal) := by norm_num
  have hRk : MemLp R p μ := hR.mono_exponent hp128
  have hLpEq : lpNorm R p μ =
      (∫ ω, ‖R ω‖ ^ (k : ℝ) ∂μ) ^ ((k : ℝ)⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hptop hRk.aestronglyMeasurable,
      hpReal]
  have hmono : eLpNorm R p μ ≤ eLpNorm R 128 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le hp128
  have hLp : lpNorm R p μ ≤ epsilon := by
    change (eLpNorm R p μ).toReal ≤ epsilon
    calc
      _ ≤ (eLpNorm R 128 μ).toReal :=
        ENNReal.toReal_mono hR.eLpNorm_ne_top hmono
      _ = lpNorm R 128 μ := rfl
      _ ≤ epsilon := hcap
  have hI0 : 0 ≤ ∫ ω, ‖R ω‖ ^ (k : ℝ) ∂μ :=
    integral_nonneg fun ω => by positivity
  have hI : (∫ ω, ‖R ω‖ ^ (k : ℝ) ∂μ) ≤ epsilon ^ k := by
    calc
      _ = ((∫ ω, ‖R ω‖ ^ (k : ℝ) ∂μ) ^ ((k : ℝ)⁻¹)) ^ (k : ℝ) := by
        rw [Real.rpow_inv_rpow hI0 (by exact_mod_cast hk.ne')]
      _ ≤ epsilon ^ k := by
        rw [← hLpEq]
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow lpNorm_nonneg hLp hkReal.le
  have hnorm : ∀ᵐ ω ∂μ, ‖R ω‖ ^ (k : ℝ) = R ω ^ k := by
    filter_upwards [hR0] with ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω, Real.rpow_natCast]
  calc
    ∫ ω, R ω ^ k ∂μ = ∫ ω, ‖R ω‖ ^ (k : ℝ) ∂μ :=
      (integral_congr_ae hnorm).symm
    _ ≤ epsilon ^ k := hI

/-- The source remainder's first three moments follow from its L128 bank row. -/
theorem main_inverse_deficit_remainder_moments_of_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (epsilon : ℝ)
    (hR : MemLp R 128 μ) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hcap : lpNorm R 128 μ ≤ epsilon) :
    (∫ ω, R ω ∂μ ≤ epsilon) ∧
      (∫ ω, R ω ^ 2 ∂μ ≤ epsilon ^ 2) ∧
      (∫ ω, R ω ^ 3 ∂μ ≤ epsilon ^ 3) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using main_inverse_deficit_remainder_moment_le_lp128 R epsilon 1
      (by norm_num) (by norm_num) hR hR0 hcap
  · exact main_inverse_deficit_remainder_moment_le_lp128 R epsilon 2
      (by norm_num) (by norm_num) hR hR0 hcap
  · exact main_inverse_deficit_remainder_moment_le_lp128 R epsilon 3
      (by norm_num) (by norm_num) hR hR0 hcap

/-- The grouped inverse bank exports its remainder as an `ℝ≥0∞` function.
After its pointwise finite-history fact, the L128 cap gives the first three
moments of the corresponding real-valued remainder. -/
theorem main_inverse_deficit_remainder_moments_of_ennreal_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Ω → ENNReal) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hfinite : ∀ᵐ ω ∂μ, R ω < ⊤)
    (hcap : eLpNorm R 128 μ ≤ ENNReal.ofReal epsilon) :
    (∫ ω, (R ω).toReal ∂μ ≤ epsilon) ∧
      (∫ ω, (R ω).toReal ^ 2 ∂μ ≤ epsilon ^ 2) ∧
      (∫ ω, (R ω).toReal ^ 3 ∂μ ≤ epsilon ^ 3) := by
  let T : Ω → ℝ := fun ω => (R ω).toReal
  have hT0 : ∀ ω, 0 ≤ T ω := fun _ => ENNReal.toReal_nonneg
  have hnorm : eLpNorm T 128 μ = eLpNorm R 128 μ := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (T ω)) 128 μ := by
        symm
        exact eLpNorm_ofReal T (Filter.Eventually.of_forall hT0)
      _ = _ := eLpNorm_congr_ae (ofReal_toReal_ae_eq hfinite)
  have hTmem : MemLp T 128 μ := by
    rw [memLp_iff, hnorm]
    exact lt_of_le_of_lt hcap ENNReal.ofReal_lt_top
  have hTcap : lpNorm T 128 μ ≤ epsilon := by
    change (eLpNorm T 128 μ).toReal ≤ epsilon
    rw [hnorm]
    calc
      _ ≤ (ENNReal.ofReal epsilon).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
      _ = epsilon := ENNReal.toReal_ofReal hepsilon
  exact main_inverse_deficit_remainder_moments_of_lp128 T epsilon hTmem
    (Filter.Eventually.of_forall hT0) hTcap

/-- Transfer a finite `ℝ≥0∞` L128 bank row to its real representative. -/
theorem main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Ω → ENNReal) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hfinite : ∀ᵐ ω ∂μ, R ω < ⊤)
    (hcap : eLpNorm R 128 μ ≤ ENNReal.ofReal epsilon) :
    MemLp (fun ω => (R ω).toReal) 128 μ ∧
      lpNorm (fun ω => (R ω).toReal) 128 μ ≤ epsilon := by
  let T : Ω → ℝ := fun ω => (R ω).toReal
  have hT0 : ∀ ω, 0 ≤ T ω := fun _ => ENNReal.toReal_nonneg
  have hnorm : eLpNorm T 128 μ = eLpNorm R 128 μ := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (T ω)) 128 μ := by
        symm
        exact eLpNorm_ofReal T (Filter.Eventually.of_forall hT0)
      _ = _ := eLpNorm_congr_ae (ofReal_toReal_ae_eq hfinite)
  have hTmem : MemLp T 128 μ := by
    rw [memLp_iff, hnorm]
    exact lt_of_le_of_lt hcap ENNReal.ofReal_lt_top
  have hTcap : lpNorm T 128 μ ≤ epsilon := by
    change (eLpNorm T 128 μ).toReal ≤ epsilon
    rw [hnorm]
    calc
      _ ≤ (ENNReal.ofReal epsilon).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
      _ = epsilon := ENNReal.toReal_ofReal hepsilon
  exact ⟨hTmem,hTcap⟩

/-- Lower powers of an L128 remainder are integrable on the finite source law. -/
theorem main_inverse_deficit_remainder_power_integrable_of_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (k : ℕ) (hk : 0 < k) (hk128 : k ≤ 128)
    (hR : MemLp R 128 μ) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω) :
    Integrable (fun ω => R ω ^ k) μ := by
  have hp128 : (k : ENNReal) ≤ 128 := by exact_mod_cast hk128
  have hRk : MemLp R k μ := hR.mono_exponent hp128
  have hnormInt : Integrable (fun ω => ‖R ω‖ ^ k) μ :=
    hRk.integrable_norm_pow hk.ne'
  have hpow : ∀ᵐ ω ∂μ, ‖R ω‖ ^ k = R ω ^ k := by
    filter_upwards [hR0] with ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  exact hnormInt.congr hpow

/-- The three power integrability facts charged by the inverse-deficit cubic. -/
theorem main_inverse_deficit_remainder_integrable_moments_of_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : MemLp R 128 μ) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω) :
    Integrable R μ ∧ Integrable (fun ω => R ω ^ 2) μ ∧
      Integrable (fun ω => R ω ^ 3) μ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using main_inverse_deficit_remainder_power_integrable_of_lp128
      R 1 (by norm_num) (by norm_num) hR hR0
  · exact main_inverse_deficit_remainder_power_integrable_of_lp128
      R 2 (by norm_num) (by norm_num) hR hR0
  · exact main_inverse_deficit_remainder_power_integrable_of_lp128
      R 3 (by norm_num) (by norm_num) hR hR0

/-- The order-128 global inverse bank makes both `d` and its cubic generator
integrand integrable whenever `0≤d≤2B`. -/
theorem main_inverse_deficit_trace_integrability_of_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B d : Ω → ℝ) (hdMeas : Measurable d)
    (hB : MemLp B 128 μ) (hB0 : ∀ᵐ ω ∂μ, 0 ≤ B ω)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * B ω) :
    Integrable d μ ∧ Integrable (fun ω => B ω ^ 2 * d ω) μ := by
  have hB1 : Integrable B μ := hB.integrable (by norm_num)
  have hB3 : MemLp B 3 μ := hB.mono_exponent (by exact_mod_cast (show 3 ≤ 128 by norm_num))
  have hBcubeNorm : Integrable (fun ω => ‖B ω‖ ^ 3) μ :=
    hB3.integrable_norm_pow (by norm_num)
  have hBcube : Integrable (fun ω => B ω ^ 3) μ := by
    apply hBcubeNorm.congr
    filter_upwards [hB0] with ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have htwoB : Integrable (fun ω => 2 * B ω) μ := by
    simpa using hB1.const_mul 2
  have hdInt : Integrable d μ :=
    htwoB.mono_nonneg hdMeas.aestronglyMeasurable
      (hd.mono fun ω hω => hω.1)
      (hd.mono fun ω hω => hω.2)
  have htwoBcube : Integrable (fun ω => 2 * B ω ^ 3) μ := by
    simpa using hBcube.const_mul 2
  have hBsqMeas : AEStronglyMeasurable (fun ω => B ω ^ 2) μ :=
    (hB.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  have hBdMeas : AEStronglyMeasurable (fun ω => B ω ^ 2 * d ω) μ :=
    hBsqMeas.mul hdMeas.aestronglyMeasurable
  have hBdInt : Integrable (fun ω => B ω ^ 2 * d ω) μ :=
    htwoBcube.mono_nonneg hBdMeas
      (hd.mono fun ω hω => mul_nonneg (sq_nonneg _) hω.1)
      (hd.mono fun ω hω => by
        calc
          B ω ^ 2 * d ω ≤ B ω ^ 2 * (2 * B ω) :=
            mul_le_mul_of_nonneg_left hω.2 (sq_nonneg _)
          _ = 2 * B ω ^ 3 := by ring)
  exact ⟨hdInt,hBdInt⟩

/-- The integrated source cubic split needs no separate remainder integrability
or moment premises once its probability-law L128 bank row is available. -/
theorem main_inverse_deficit_cubic_integral_bound_of_lp128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (beta epsilon : ℝ) (B d R : Ω → ℝ)
    (hbeta : 0 ≤ beta) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hB : ∀ᵐ ω ∂μ, B ω ≤ beta + R ω)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * B ω)
    (hBdInt : Integrable (fun ω => B ω ^ 2 * d ω) μ)
    (hdInt : Integrable d μ)
    (hR : MemLp R 128 μ) (hcap : lpNorm R 128 μ ≤ epsilon) :
    ∫ ω, B ω ^ 2 * d ω ∂μ ≤
      beta ^ 2 * (∫ ω, d ω ∂μ) +
        2 * (2 * beta ^ 2 * epsilon + 3 * beta * epsilon ^ 2 + epsilon ^ 3) := by
  have hRints := main_inverse_deficit_remainder_integrable_moments_of_lp128
    R hR hR0
  have hMom := main_inverse_deficit_remainder_moments_of_lp128
    R epsilon hR hR0 hcap
  have hbase := main_inverse_deficit_cubic_integral_bound μ beta B d R
    hbeta hR0 hB hd
    hBdInt hdInt hRints.1 hRints.2.1 hRints.2.2
  have hsum :
      2 * beta ^ 2 * (∫ ω, R ω ∂μ) +
          3 * beta * (∫ ω, R ω ^ 2 ∂μ) + ∫ ω, R ω ^ 3 ∂μ ≤
        2 * beta ^ 2 * epsilon + 3 * beta * epsilon ^ 2 + epsilon ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_left hMom.1 (by positivity : 0 ≤ 2 * beta ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hMom.2.1 (by positivity : 0 ≤ 3 * beta)
    nlinarith [h1, h2, hMom.2.2]
  calc
    _ ≤ beta ^ 2 * (∫ ω, d ω ∂μ) +
        2 * (2 * beta ^ 2 * (∫ ω, R ω ∂μ) +
          3 * beta * (∫ ω, R ω ^ 2 ∂μ) + ∫ ω, R ω ^ 3 ∂μ) := hbase
    _ ≤ _ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by norm_num))

/-- Combine the global inverse L128 cap and the remainder L128 cap in the
integrated cubic source bound. -/
theorem main_inverse_deficit_cubic_integral_bound_of_l128_banks
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (beta epsilon : ℝ) (B d R : Ω → ℝ)
    (hbeta : 0 ≤ beta) (hR0 : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hBsplit : ∀ᵐ ω ∂μ, B ω ≤ beta + R ω)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * B ω)
    (hdMeas : Measurable d)
    (hB : MemLp B 128 μ) (hR : MemLp R 128 μ)
    (hcap : lpNorm R 128 μ ≤ epsilon) :
    ∫ ω, B ω ^ 2 * d ω ∂μ ≤
      beta ^ 2 * (∫ ω, d ω ∂μ) +
        2 * (2 * beta ^ 2 * epsilon + 3 * beta * epsilon ^ 2 + epsilon ^ 3) := by
  have hB0 : ∀ᵐ ω ∂μ, 0 ≤ B ω := hd.mono fun ω hω => by
    rcases hω with ⟨hd0, hdle⟩
    linarith
  have hIntegrable := main_inverse_deficit_trace_integrability_of_lp128
    B d hdMeas hB hB0 hd
  exact main_inverse_deficit_cubic_integral_bound_of_lp128 beta epsilon B d R
    hbeta hR0 hBsplit hd hIntegrable.2 hIntegrable.1 hR hcap

/-- Form of the integrated cubic estimate for the extended
nonnegative global-history and remainder banks. -/
theorem main_inverse_deficit_cubic_integral_bound_of_ennreal_l128_banks
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (beta epsilon : ℝ) (B R : Ω → ENNReal) (d : Ω → ℝ)
    (hbeta : 0 ≤ beta) (hepsilon : 0 ≤ epsilon)
    (hBsplit : ∀ᵐ ω ∂μ, (B ω).toReal ≤ beta + (R ω).toReal)
    (hd : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * (B ω).toReal)
    (hdMeas : Measurable d)
    (hBfinite : ∀ᵐ ω ∂μ, B ω < ⊤)
    (hBcap : eLpNorm B 128 μ ≤ ENNReal.ofReal beta)
    (hRfinite : ∀ᵐ ω ∂μ, R ω < ⊤)
    (hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal epsilon) :
    ∫ ω, (B ω).toReal ^ 2 * d ω ∂μ ≤
      beta ^ 2 * (∫ ω, d ω ∂μ) +
        2 * (2 * beta ^ 2 * epsilon + 3 * beta * epsilon ^ 2 + epsilon ^ 3) := by
  have hBmem := main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    B beta hbeta hBfinite hBcap
  have hRmem := main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    R epsilon hepsilon hRfinite hRcap
  have hR0 : ∀ ω, 0 ≤ (R ω).toReal := fun _ => ENNReal.toReal_nonneg
  exact main_inverse_deficit_cubic_integral_bound_of_l128_banks
    beta epsilon (fun ω => (B ω).toReal) d (fun ω => (R ω).toReal)
    hbeta (Filter.Eventually.of_forall hR0) hBsplit hd hdMeas
    hBmem.1 hRmem.1 hRmem.2

/-- The relative error factor in the OLD absolute inverse-deficit branch. -/
noncomputable def mainInverseDeficitRelativeError (beta epsilon : ℝ) : ℝ :=
  4 * epsilon + 6 * epsilon ^ 2 / beta + 2 * epsilon ^ 3 / beta ^ 2

theorem mainInverseDeficitRelativeError_nonneg {beta epsilon : ℝ}
    (hbeta : 0 < beta) (hepsilon : 0 ≤ epsilon) :
    0 ≤ mainInverseDeficitRelativeError beta epsilon := by
  unfold mainInverseDeficitRelativeError
  positivity

/-- A lower differential inequality for the actual inverse trace gives the
source absolute branch by an integrating factor. The source generator adapter
can supply `hderiv` once its pathwise and heat inputs are instantiated. -/
theorem main_inverse_deficit_absolute_branch_of_deriv
    {u : ℝ → ℝ} {r kappa v t : ℝ}
    (hkappa : 0 < kappa)
    (hv : 0 ≤ v)
    (hAC : AbsolutelyContinuousOnInterval u 0 1)
    (hinit : 2 ≤ u 0)
    (hderiv : ∀ᵐ s, s ∈ Icc (0 : ℝ) 1 →
      -kappa * u s - kappa * r ≤ deriv u s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    -v * (u t - 2) ≤
      v * (2 + r) *
        (1 - Real.exp (-kappa * t)) := by
  have hnegACmul : AbsolutelyContinuousOnInterval (fun s => (-1 : ℝ) * u s) 0 1 :=
    AbsolutelyContinuousOnInterval.const_mul (-1) hAC
  have hnegAC : AbsolutelyContinuousOnInterval (fun s => -u s) 0 1 := by
    have hfun : (fun s => -u s) = (fun s => (-1 : ℝ) * u s) := by
      funext s
      ring
    rw [hfun]
    exact hnegACmul
  have hnegDeriv : ∀ᵐ s, s ∈ Icc (0 : ℝ) 1 →
      deriv (fun x => -u x) s ≤ kappa * r - kappa * (-(u s)) := by
    filter_upwards [hAC.ae_differentiableAt, hderiv] with s hs hd hs01
    have hs' : s ∈ uIcc (0 : ℝ) 1 := by
      rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hderiv' : HasDerivAt (fun x => -u x) (-deriv u s) s :=
      (hs hs').hasDerivAt.neg
    rw [hderiv'.deriv]
    have hsource := hd hs01
    change -kappa * u s - kappa * r ≤ deriv u s at hsource
    calc
      -deriv u s ≤ kappa * u s + kappa * r := by linarith
      _ = kappa * r - kappa * (-(u s)) := by ring
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have hcomparison := panel_comparison_on hab hnegAC hkappa hnegDeriv ht
  have hinitialNeg : -u 0 ≤ -2 := by linarith
  have hcomparison' : -u t ≤ panelMap (kappa * r) kappa t (-2) := by
    have h := hcomparison.trans
      (panelMap_mono (kappa * r) kappa (t - 0) hinitialNeg)
    simpa only [sub_zero] using h
  have hpanel : panelMap (kappa * r) kappa t (-2) =
      -2 * Real.exp (-kappa * t) + r * (1 - Real.exp (-kappa * t)) := by
    unfold panelMap
    field_simp [hkappa.ne']
  have hnegativeBound : -u t ≤
      -2 * Real.exp (-kappa * t) + r * (1 - Real.exp (-kappa * t)) := by
    rw [hpanel] at hcomparison'
    exact hcomparison'
  have hbranch : 2 - u t ≤
      (2 + r) * (1 - Real.exp (-kappa * t)) := by
    calc
      2 - u t = -u t + 2 := by ring
      _ ≤ -2 * Real.exp (-kappa * t) +
          r * (1 - Real.exp (-kappa * t)) + 2 := add_le_add_left hnegativeBound 2
      _ = (2 + r) * (1 - Real.exp (-kappa * t)) := by ring
  calc
    -v * (u t - 2) = v * (2 - u t) := by ring
    _ ≤ v * ((2 + r) * (1 - Real.exp (-kappa * t))) :=
      mul_le_mul_of_nonneg_left hbranch hv
    _ = v * (2 + r) * (1 - Real.exp (-kappa * t)) := by ring

/-- The source-coefficient specialization used by MA-INVERSE-DEFICIT. -/
theorem main_inverse_deficit_absolute_branch
    {u : ℝ → ℝ} {beta epsilon kappa v t : ℝ}
    (_hbeta : 0 < beta) (_hepsilon : 0 ≤ epsilon) (hkappa : 0 < kappa)
    (hv : 0 ≤ v)
    (hAC : AbsolutelyContinuousOnInterval u 0 1)
    (hinit : 2 ≤ u 0)
    (hderiv : ∀ᵐ s, s ∈ Icc (0 : ℝ) 1 →
      -kappa * u s - kappa * mainInverseDeficitRelativeError beta epsilon ≤ deriv u s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    -v * (u t - 2) ≤
      v * (2 + 4 * epsilon + 6 * epsilon ^ 2 / beta + 2 * epsilon ^ 3 / beta ^ 2) *
        (1 - Real.exp (-kappa * t)) := by
  have h := main_inverse_deficit_absolute_branch_of_deriv
    (r := mainInverseDeficitRelativeError beta epsilon)
    hkappa hv hAC hinit hderiv ht
  calc
    -v * (u t - 2) ≤
        v * (2 + mainInverseDeficitRelativeError beta epsilon) *
          (1 - Real.exp (-kappa * t)) := h
    _ = v * (2 + 4 * epsilon + 6 * epsilon ^ 2 / beta +
        2 * epsilon ^ 3 / beta ^ 2) * (1 - Real.exp (-kappa * t)) := by
      unfold mainInverseDeficitRelativeError
      ring

/-- Source-fixed absolute branch with the MA channel coefficients and global
bank constants. Its only remaining analytic input is the actual lower
differential inequality supplied by the heat identity and trace generator. -/
theorem main_inverse_deficit_absolute_branch_source
    {u : ℝ → ℝ} {v t : ℝ}
    (hmu : 0 < mainInverseMuMinusSource v)
    (hv : 0 ≤ v)
    (hAC : AbsolutelyContinuousOnInterval u 0 1)
    (hinit : 2 ≤ u 0)
    (hderiv : ∀ᵐ s, s ∈ Icc (0 : ℝ) 1 →
      -mainKappa (mainInverseMuMinusSource v) * u s -
        mainKappa (mainInverseMuMinusSource v) * mainRho ≤ deriv u s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    -v * (u t - 2) ≤ mainInverseAbs v (mainInverseMuMinusSource v) t := by
  have hbeta : 0 < mainBeta := by norm_num [mainBeta]
  have hepsilon : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
  have hkappa : 0 < mainKappa (mainInverseMuMinusSource v) := by
    unfold mainKappa
    exact mul_pos hmu (sq_pos_of_pos hbeta)
  have hrho : mainInverseDeficitRelativeError mainBeta mainEpsNew = mainRho := by
    rfl
  have hderiv' : ∀ᵐ s, s ∈ Icc (0 : ℝ) 1 →
      -mainKappa (mainInverseMuMinusSource v) * u s -
        mainKappa (mainInverseMuMinusSource v) *
          mainInverseDeficitRelativeError mainBeta mainEpsNew ≤ deriv u s := by
    filter_upwards [hderiv] with s hs hs01
    rw [hrho]
    exact hs hs01
  have hbranch := main_inverse_deficit_absolute_branch
    hbeta hepsilon hkappa hv hAC hinit hderiv' ht
  calc
    -v * (u t - 2) ≤
        v * (2 + 4 * mainEpsNew + 6 * mainEpsNew ^ 2 / mainBeta +
          2 * mainEpsNew ^ 3 / mainBeta ^ 2) *
          (1 - Real.exp (-mainKappa (mainInverseMuMinusSource v) * t)) := hbranch
    _ = mainInverseAbs v (mainInverseMuMinusSource v) t := by
      have hexp : -mainKappa (mainInverseMuMinusSource v) * t =
          -(mainKappa (mainInverseMuMinusSource v) * t) := by ring
      rw [hexp]
      unfold mainInverseAbs mainRho
      ring

end ASDExplicitGamma.Main

end
