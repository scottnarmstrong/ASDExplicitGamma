/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.SmallGammaSeed
public import ASDExplicitGamma.Cold.NativeTrace
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Numerics.AllOrder.Allocations
public import ASDExplicitGamma.Numerics.AllOrder.CirReadable
public import ASDExplicitGamma.Main.FrameMap
public import ASDExplicitGamma.Gaussian.ShellFrameClock
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Finite-even CIR induction and source seeds -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- The least even integer not below a real order, with a floor at twelve. -/
noncomputable def aoCirEvenCeiling (p : ℝ) : ℕ :=
  2 * Nat.ceil (max 6 (p / 2))

/-- Finite-even caps imply the source real-order fill on a probability space.
The premise is exactly a finite-order cap, including the integrability that
makes comparison of the real Lp norms legitimate. -/
theorem aoCir_real_order_fill_of_even_caps
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {P : ℕ} (hP : 20 ≤ P) (hPeven : Even P)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hcap : ∀ q : ℕ, 12 ≤ q → Even q → q ≤ P →
      MemLp X (q : ℝ≥0∞) μ ∧
        lpNorm X (q : ℝ≥0∞) μ ≤ 900000 * γ * (q : ℝ))
    {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ (P : ℝ)) :
    lpNorm X (ENNReal.ofReal p) μ ≤ 2 * 900000 * γ * p + 12 * 900000 * γ := by
  let q : ℕ := aoCirEvenCeiling p
  have hq12 : 12 ≤ q := by
    dsimp [q, aoCirEvenCeiling]
    have h6real : (6 : ℝ) ≤ (Nat.ceil (max 6 (p / 2)) : ℝ) :=
      (le_max_left (6 : ℝ) (p / 2)).trans (Nat.le_ceil _)
    have h6 : 6 ≤ Nat.ceil (max 6 (p / 2)) := by exact_mod_cast h6real
    omega
  have hqEven : Even q := by
    dsimp [q, aoCirEvenCeiling]
    exact even_two_mul _
  have hp2 : 0 ≤ p / 2 := by positivity
  have hPReal : (20 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hmaxP : max 6 (p / 2) ≤ (P : ℝ) / 2 := by
    apply max_le
    · linarith
    · linarith
  have hqP : q ≤ P := by
    dsimp [q, aoCirEvenCeiling]
    obtain ⟨k, hk⟩ := hPeven
    have hkCast : (P : ℝ) / 2 = (k : ℝ) := by rw [hk]; norm_num
    have hceil : Nat.ceil (max 6 (p / 2)) ≤ k := by
      rw [Nat.ceil_le]
      rw [hkCast] at hmaxP
      exact hmaxP
    rw [hk]
    omega
  have hpq : p ≤ (q : ℝ) := by
    have hle : p / 2 ≤ max 6 (p / 2) := le_max_right _ _
    have hceil : p / 2 ≤ (Nat.ceil (max 6 (p / 2)) : ℝ) :=
      hle.trans (Nat.le_ceil _)
    dsimp [q, aoCirEvenCeiling]
    push_cast
    nlinarith
  have hqCeil : (q : ℝ) ≤ 2 * p + 12 := by
    by_cases hp12 : p < 12
    · have hmax : max 6 (p / 2) = 6 := max_eq_left (by linarith)
      simp [q, aoCirEvenCeiling, hmax]
      linarith
    · have hmax : max 6 (p / 2) = p / 2 := max_eq_right (by linarith)
      dsimp [q, aoCirEvenCeiling]
      have hceil : (Nat.ceil (max 6 (p / 2)) : ℝ) < max 6 (p / 2) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      rw [hmax] at hceil ⊢
      push_cast
      nlinarith
  have hc := hcap q hq12 hqEven hqP
  have hExp : ENNReal.ofReal p ≤ (q : ℝ≥0∞) := by
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal (q : ℝ) := ENNReal.ofReal_le_ofReal hpq
      _ = (q : ℝ≥0∞) := by norm_cast
  have hnorm : lpNorm X (ENNReal.ofReal p) μ ≤ lpNorm X (q : ℝ≥0∞) μ := by
    unfold lpNorm
    exact ENNReal.toReal_mono hc.1.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hExp)
  calc
    lpNorm X (ENNReal.ofReal p) μ ≤ 900000 * γ * (q : ℝ) := hnorm.trans hc.2
    _ ≤ 900000 * γ * (2 * p + 12) := by
      exact mul_le_mul_of_nonneg_left hqCeil (by positivity)
    _ = 2 * 900000 * γ * p + 12 * 900000 * γ := by ring

/-- The two real-order cutoff gates for the source staircase. -/
theorem aoCir_small_gamma_seed_order_gates {γ : ℝ} (hγ : 0 < γ) :
    γ * (smallGammaSeedP γ : ℝ) > 1 / 19000 ∧
      (48 : ℝ) ≤ 4 * (smallGammaSeedP γ : ℝ) := by
  let x : ℝ := (1 / 16384 : ℝ) / (2 * γ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hfloorInt : (⌊x⌋₊ : ℤ) = (⌊x⌋ : ℤ) :=
    Int.natCast_floor_eq_floor hx
  have hfloor : (⌊x⌋₊ : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast hfloorInt
  have hP : (smallGammaSeedP γ : ℝ) =
      max 20 (2 * (⌊x⌋ : ℤ) : ℝ) := by
    simp only [smallGammaSeedP, Nat.cast_max, Nat.cast_ofNat, Nat.cast_mul,
      hfloor, x]
  have h := Numerics.AllOrder.seed_order_gates γ hγ
  simpa only [hP] using h

/-- In the large-gamma branch, the finite cutoff collapses to order twenty. -/
theorem aoCir_large_gamma_cutoff_eq_twenty {γ : ℝ}
    (hγ : (1 / 327680 : ℝ) < γ) : smallGammaSeedP γ = 20 := by
  unfold smallGammaSeedP
  let x : ℝ := (1 / 16384 : ℝ) / (2 * γ)
  have hden : 0 < 2 * γ := by linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx : x < 10 := by
    dsimp [x]
    apply (div_lt_iff₀ hden).2
    norm_num at hγ ⊢
    linarith
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hcast : (⌊x⌋₊ : ℝ) < 10 := hfloor.trans_lt hx
  have hnat : ⌊x⌋₊ < 10 := by exact_mod_cast hcast
  have htwice : 2 * ⌊x⌋₊ ≤ 20 := by omega
  change max 20 (2 * ⌊x⌋₊) = 20
  exact max_eq_left htwice

/-- The large-gamma frozen state supplies the actual root and mean caps needed by
the finite-even source argument. The p=20 root is quantitatively below
`593 γ`, while the ordinary mean is below `177 γ`. -/
theorem aoCir_large_gamma_native_seed (M : ABKModel 2) (h : ℝ)
    (hγ : (1 / 327680 : ℝ) < M.gamma)
    (hγ0 : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h m) :
    smallGammaSeedP M.gamma = 20 ∧
      lpNorm (cutoffTraceDefect M m m) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ 593 * M.gamma ∧
      593 * M.gamma < 5000 * M.gamma ∧
      Cold.coldNativeMean M m 0 ≤ 177 * M.gamma := by
  have hP := aoCir_large_gamma_cutoff_eq_twenty hγ
  have htheta : theta M ≤ 1 := by
    apply (div_le_one (by norm_num [gammaZero] : (0 : ℝ) < gammaZero)).2
    simpa only [theta] using hγ0
  have htheta0 : 0 < theta M :=
    div_pos M.shellPrefix.gamma_pos (by norm_num [gammaZero])
  have hrootState : root20 M m ≤ ENNReal.ofReal (2013 / 10000 * theta M) := hstate.2.2.1
  have hrootNonneg : 0 ≤ 2013 / 10000 * theta M := by positivity
  have hrootNorm := Cold.coldNativeTrace_zero_norm_le hrootNonneg hrootState
  have hrootReal : lpNorm (cutoffTraceDefect M m m) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ 2013 / 10000 * theta M := by
    simpa only [Cold.coldNativeTrace, Int.natCast_zero, add_zero] using hrootNorm
  have hfactor : (2013 / 10000 : ℝ) / gammaZero ≤ 593 := by
    norm_num [gammaZero]
  have hrootGamma : 2013 / 10000 * theta M ≤ 593 * M.gamma := by
    rw [theta]
    calc
      (2013 / 10000) * (M.gamma / gammaZero) =
          ((2013 / 10000) / gammaZero) * M.gamma := by ring
      _ ≤ 593 * M.gamma := mul_le_mul_of_nonneg_right hfactor (le_of_lt M.shellPrefix.gamma_pos)
  have hmeanState : ordinaryMean M m ≤ ENNReal.ofReal (3 / 50 * theta M) := hstate.1
  have hmean0 := Cold.coldNativeMean_zero_le (by positivity) hmeanState
  have hmeanGamma : Cold.coldNativeMean M m 0 ≤ 177 * M.gamma := by
    have hmeanFactor : (3 / 50 : ℝ) / gammaZero ≤ 177 := by
      norm_num [gammaZero]
    calc
      Cold.coldNativeMean M m 0 ≤ 3 / 50 * theta M := hmean0
      _ = ((3 / 50 : ℝ) / gammaZero) * M.gamma := by rw [theta]; ring
      _ ≤ 177 * M.gamma := mul_le_mul_of_nonneg_right hmeanFactor (le_of_lt M.shellPrefix.gamma_pos)
  refine ⟨hP, hrootReal.trans hrootGamma, ?_, hmeanGamma⟩
  have hgammaPos := M.shellPrefix.gamma_pos
  nlinarith

/-- Restore the true completed frame after eight shells.  The structural
continuity ratio is paid explicitly, and the additive change is at most γ in
the small-gamma range. -/
theorem aoCir_eight_shell_frame_restore (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (hγ : M.gamma ≤ 1 / 327680) :
    cutoffTraceDefect M m m ω ≤
      (1017 / 1000 : ℝ) *
        traceDefect (cubeSet (originCube 2 m))
          (Cutoff.coefficientCutoff M.nu m ω).toFun
          (Annealed.sigmaBar M (m - 8) : ℝ) + M.gamma := by
  let σold : ℝ := Annealed.sigmaBar M (m - 8)
  let σnew : ℝ := Annealed.sigmaBar M m
  let ρ : ℝ := σnew / σold
  let Told : ℝ := traceDefect (cubeSet (originCube 2 m))
    (Cutoff.coefficientCutoff M.nu m ω).toFun σold
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hframe := Scalar.sigmaBar_structural_continuity M (m - 8) 8 (by omega)
  have hexp : (2 : ℝ) * M.gamma * 8 = 16 * M.gamma := by ring
  have hρ : ρ ≤ (3 : ℝ) ^ (16 * M.gamma) := by
    dsimp [ρ, σnew, σold]
    have hf := hframe.2
    rw [Real.rpow_eq_pow] at hf
    simpa only [Int.sub_add_cancel, Int.cast_ofNat, hexp] using hf
  have hpow : (3 : ℝ) ^ (16 * M.gamma) ≤
      (3 : ℝ) ^ (16 / 327680 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hclock : ρ ≤ 1001 / 1000 :=
    (hρ.trans hpow).trans (le_of_lt Numerics.AllOrder.cir_radical_caps.2.2.2.2.2.2)
  obtain ⟨Λ, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω (originCube 2 m)
  have hTold : 0 ≤ Told :=
    Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M (m - 8)).1
  have hmap := Main.main_cutoff_pathwise_frame_map M (m - 8) m m ω (by omega)
    (1 / 100 : ℝ) (by norm_num)
  have hmap' : cutoffTraceDefect M m m ω ≤
      ρ * ((101 / 100 : ℝ) * Told +
        8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * M.gamma * 9) ^ 2) := by
    have hgap : (m - (m - 8) : ℤ) = 8 := by omega
    norm_num [ρ, σold, σnew, Told, hgap] at hmap ⊢
    exact hmap
  have hmult : ρ * (101 / 100 : ℝ) ≤ 1017 / 1000 := by
    nlinarith [hclock]
  have hC : 0 ≤ 8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * 9) ^ 2 := by positivity
  have hCsmall : (1001 / 1000 : ℝ) *
      (8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * 9) ^ 2) * M.gamma ≤ 1 := by
    norm_num at hγ ⊢
    nlinarith
  have hadd : ρ * (8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * 9) ^ 2) * M.gamma ^ 2 ≤
      M.gamma := by
    calc
      _ ≤ (1001 / 1000 : ℝ) *
          (8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * 9) ^ 2) * M.gamma ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hclock hC) (sq_nonneg M.gamma)
      _ ≤ M.gamma := by nlinarith [hCsmall, hγ0]
  calc
    cutoffTraceDefect M m m ω ≤
        ρ * ((101 / 100 : ℝ) * Told +
          8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * M.gamma * 9) ^ 2) := hmap'
    _ = ρ * (101 / 100 : ℝ) * Told +
        ρ * (8 * (1 + 100 : ℝ) * ((11 / 10 : ℝ) * 9) ^ 2) * M.gamma ^ 2 := by ring
    _ ≤ (1017 / 1000 : ℝ) * Told + M.gamma :=
      add_le_add (mul_le_mul_of_nonneg_right hmult hTold) hadd

/-- The native scalar corridor pays the source variance clock over a band of
at most eight inserted shells, with the exact largest growth factor
`3^(16 γ)`. -/
theorem aoCir_native_eight_shell_clock (M : ABKModel 2) (h : ℝ)
    (k i : ℤ) (hi : i ≤ k + 8)
    (hstate : nativeInductionState M h k) :
    ASDExplicitGamma.Gaussian.q3ModelAmplitude M h i ^ 2 /
      (Annealed.sigmaBar M k : ℝ) ^ 2 ≤
        (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (16 * M.gamma) := by
  have hγ := M.shellPrefix.gamma_pos
  let δ := 1 - (3 : ℝ) ^ (-(2 * M.gamma))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (mul_pos (by norm_num) hγ))
  have hδbound : δ ≤ (9 / 2 : ℝ) * (49 / 100) * M.gamma := by
    have he := Real.add_one_le_exp (-(2 * M.gamma) * Real.log 3)
    have hc := mul_le_mul_of_nonneg_right
      Numerics.Scalar.lower_clock_margins.2.le hγ.le
    dsimp [δ]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [mul_comm (Real.log 3)]
    linarith only [he, hc]
  obtain ⟨_, _, _, _, _, _, hlower, _⟩ := hstate
  have hsigma := (Annealed.sigmaBar_characterization M k).1
  have hvariance0 : 0 ≤ shellVarianceSum h M.gamma k := by
    unfold shellVarianceSum
    positivity
  have hquarter : (49 / 100 : ℝ) * shellVarianceSum h M.gamma k ≤
      (Annealed.sigmaBar M k : ℝ) ^ 2 := by
    have hnu := sq_nonneg M.nu
    nlinarith only [hlower, hvariance0, hnu]
  have hbase : h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) ≤
      (Annealed.sigmaBar M k : ℝ) ^ 2 * (δ / (49 / 100 : ℝ)) := by
    have hb : (49 / 100 : ℝ) *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ≤
        (Annealed.sigmaBar M k : ℝ) ^ 2 * δ := by
      apply (div_le_iff₀ hδ).mp
      simpa only [shellVarianceSum, δ, mul_div_assoc] using hquarter
    calc
      h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) =
          (49 / 100 : ℝ)⁻¹ * ((49 / 100 : ℝ) *
            (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))) := by field_simp
      _ ≤ (49 / 100 : ℝ)⁻¹ *
          ((Annealed.sigmaBar M k : ℝ) ^ 2 * δ) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (Annealed.sigmaBar M k : ℝ) ^ 2 * (δ / (49 / 100 : ℝ)) := by
        field_simp
  have hexp : (3 : ℝ) ^ (2 * M.gamma * (i : ℝ)) =
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - k)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hgrowth : (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - k)) ≤
      (3 : ℝ) ^ (16 * M.gamma) := by
    have hiR : (i : ℝ) - (k : ℝ) ≤ 8 := by exact_mod_cast (show i - k ≤ 8 by omega)
    have hexp : 2 * M.gamma * ((i : ℝ) - (k : ℝ)) ≤ 16 * M.gamma := by
      have := mul_le_mul_of_nonneg_left hiR (by positivity : 0 ≤ 2 * M.gamma)
      nlinarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      hexp
  apply (div_le_iff₀ (sq_pos_of_pos hsigma)).mpr
  rw [ASDExplicitGamma.Gaussian.q3ModelAmplitude_sq, hexp, ← mul_assoc]
  calc
    _ ≤ ((Annealed.sigmaBar M k : ℝ) ^ 2 *
        (δ / (49 / 100 : ℝ))) *
          (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - k)) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ ≤ ((Annealed.sigmaBar M k : ℝ) ^ 2 *
        ((9 / 2 : ℝ) * M.gamma)) *
          (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - k)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith only [hδbound]
    _ ≤ ((Annealed.sigmaBar M k : ℝ) ^ 2 *
        ((9 / 2 : ℝ) * M.gamma)) * (3 : ℝ) ^ (16 * M.gamma) :=
      mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ = _ := by ring

/-- The native variance clock at an arbitrary later shell label, with its
exact exponential depth factor left visible. -/
theorem aoCir_native_shell_clock_depth (M : ABKModel 2) (h : ℝ)
    (k i : ℤ) (hki : k ≤ i)
    (hstate : nativeInductionState M h k) :
    ASDExplicitGamma.Gaussian.q3ModelAmplitude M h i ^ 2 /
      (Annealed.sigmaBar M k : ℝ) ^ 2 ≤
        (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * ((i - k : ℤ) : ℝ)) := by
  have hγ := M.shellPrefix.gamma_pos
  let δ := 1 - (3 : ℝ) ^ (-(2 * M.gamma))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (mul_pos (by norm_num) hγ))
  have hδbound : δ ≤ (9 / 2 : ℝ) * (49 / 100) * M.gamma := by
    have he := Real.add_one_le_exp (-(2 * M.gamma) * Real.log 3)
    have hc := mul_le_mul_of_nonneg_right
      Numerics.Scalar.lower_clock_margins.2.le hγ.le
    dsimp [δ]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [mul_comm (Real.log 3)]
    linarith only [he, hc]
  obtain ⟨_, _, _, _, _, _, hlower, _⟩ := hstate
  have hsigma := (Annealed.sigmaBar_characterization M k).1
  have hvariance0 : 0 ≤ shellVarianceSum h M.gamma k := by
    unfold shellVarianceSum
    positivity
  have hquarter : (49 / 100 : ℝ) * shellVarianceSum h M.gamma k ≤
      (Annealed.sigmaBar M k : ℝ) ^ 2 := by
    have hnu := sq_nonneg M.nu
    nlinarith only [hlower, hvariance0, hnu]
  have hbase : h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) ≤
      (Annealed.sigmaBar M k : ℝ) ^ 2 * (δ / (49 / 100 : ℝ)) := by
    have hb : (49 / 100 : ℝ) *
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ≤
        (Annealed.sigmaBar M k : ℝ) ^ 2 * δ := by
      apply (div_le_iff₀ hδ).mp
      simpa only [shellVarianceSum, δ, mul_div_assoc] using hquarter
    calc
      h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) =
          (49 / 100 : ℝ)⁻¹ * ((49 / 100 : ℝ) *
            (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)))) := by field_simp
      _ ≤ (49 / 100 : ℝ)⁻¹ *
          ((Annealed.sigmaBar M k : ℝ) ^ 2 * δ) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (Annealed.sigmaBar M k : ℝ) ^ 2 * (δ / (49 / 100 : ℝ)) := by
        field_simp
  have hexp : (3 : ℝ) ^ (2 * M.gamma * (i : ℝ)) =
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (3 : ℝ) ^ (2 * M.gamma * ((i - k : ℤ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hgammaNonneg : 0 ≤ M.gamma := hγ.le
  have hpowNonneg : 0 ≤ (3 : ℝ) ^ (2 * M.gamma * ((i - k : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  apply (div_le_iff₀ (sq_pos_of_pos hsigma)).mpr
  rw [ASDExplicitGamma.Gaussian.q3ModelAmplitude_sq, hexp, ← mul_assoc]
  calc
    _ ≤ ((Annealed.sigmaBar M k : ℝ) ^ 2 *
        (δ / (49 / 100 : ℝ))) *
          (3 : ℝ) ^ (2 * M.gamma * ((i - k : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hbase hpowNonneg
    _ ≤ ((Annealed.sigmaBar M k : ℝ) ^ 2 *
        ((9 / 2 : ℝ) * M.gamma)) *
          (3 : ℝ) ^ (2 * M.gamma * ((i - k : ℤ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hpowNonneg
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith only [hδbound]
    _ = _ := by ring

/-- The concrete small-gamma recurrence budget contracts by the certified
fourteen-percent margin, once the source's native-mean, centered-average, and
eight-shell transport terms have been assembled. -/
theorem aoCir_small_gamma_step_contraction {γ p : ℝ}
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 327680) (hp : 12 ≤ p) :
    (1017 / 1000 : ℝ) *
        (700 * γ + 144 * (900000 * γ) *
          (3 * Real.sqrt p / 3 ^ 8 + 9 * p / 3 ^ 16) +
          (107 / 12) * p * (9 / 2) * γ * 8 * (3 : ℝ) ^ (16 * γ) *
            (2.2 : ℝ) ^ 2 * 50) + γ ≤
      (14 / 100 : ℝ) * (900000 * γ * p) := by
  let C : ℝ := 900000 * γ * p
  have hC : 0 < C := by dsimp [C]; positivity
  have hp0 : 0 < p := by linarith
  have hroot12 : 0 < Real.sqrt 12 := Real.sqrt_pos.mpr (by norm_num)
  have hrootp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hrootle : Real.sqrt 12 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by linarith)
  have hsqrt : Real.sqrt p ≤ p / Real.sqrt 12 := by
    calc
      Real.sqrt p = p / Real.sqrt p := by
        have hsquare := Real.sq_sqrt hp0.le
        field_simp [ne_of_gt hrootp]
        nlinarith
      _ ≤ p / Real.sqrt 12 :=
        div_le_div_of_nonneg_left (by positivity) hroot12 hrootle
  have hmean : 700 * γ ≤ (700 / (12 * 900000 : ℝ)) * C := by
    calc
      700 * γ = (700 / (12 * 900000 : ℝ)) * (900000 * γ * 12) := by ring
      _ ≤ (700 / (12 * 900000 : ℝ)) * C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [C]
        nlinarith
  have hcenterOne :
      144 * (900000 * γ) * (3 * Real.sqrt p / 3 ^ 8) ≤
        (144 * (3 / (3 ^ 8 * Real.sqrt 12))) * C := by
    have hbase : 3 * Real.sqrt p / 3 ^ 8 ≤ p * (3 / (3 ^ 8 * Real.sqrt 12)) := by
      calc
        3 * Real.sqrt p / 3 ^ 8 = (3 / 3 ^ 8) * Real.sqrt p := by ring
        _ ≤ (3 / 3 ^ 8) * (p / Real.sqrt 12) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = p * (3 / (3 ^ 8 * Real.sqrt 12)) := by field_simp
    calc
      _ = (144 * (900000 * γ)) * (3 * Real.sqrt p / 3 ^ 8) := by ring
      _ ≤ (144 * (900000 * γ)) * (p * (3 / (3 ^ 8 * Real.sqrt 12))) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = (144 * (3 / (3 ^ 8 * Real.sqrt 12))) * C := by dsimp [C]; ring
  have hcenterTwo :
      144 * (900000 * γ) * (9 * p / 3 ^ 16) =
        (144 * (9 / 3 ^ 16)) * C := by dsimp [C]; ring
  have hpow : (3 : ℝ) ^ (16 * γ) ≤ (3 : ℝ) ^ (16 / 327680 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by nlinarith)
  let A : ℝ := (107 / 12) * (9 / 2) * 8 * (2.2 : ℝ) ^ 2 * 50
  have htransport :
      (107 / 12) * p * (9 / 2) * γ * 8 * (3 : ℝ) ^ (16 * γ) *
          (2.2 : ℝ) ^ 2 * 50 ≤
        (A * (3 : ℝ) ^ (16 / 327680 : ℝ) / 900000) * C := by
    calc
      _ = (A * (3 : ℝ) ^ (16 * γ)) * (γ * p) := by dsimp [A]; ring
      _ ≤ (A * (3 : ℝ) ^ (16 / 327680 : ℝ)) * (γ * p) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by dsimp [A]; positivity))
          (mul_nonneg hγ.le hp0.le)
      _ = (A * (3 : ℝ) ^ (16 / 327680 : ℝ) / 900000) * C := by
        dsimp [C]
        field_simp
  have hadd : γ ≤ (1 / (12 * 900000 : ℝ)) * C := by
    calc
      γ = (1 / (12 * 900000 : ℝ)) * (900000 * γ * 12) := by ring
      _ ≤ (1 / (12 * 900000 : ℝ)) * C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [C]
        nlinarith
  have hinside :
      700 * γ + 144 * (900000 * γ) *
          (3 * Real.sqrt p / 3 ^ 8 + 9 * p / 3 ^ 16) +
          (107 / 12) * p * (9 / 2) * γ * 8 * (3 : ℝ) ^ (16 * γ) *
            (2.2 : ℝ) ^ 2 * 50 ≤
        (700 / (12 * 900000 : ℝ) +
          144 * (3 / (3 ^ 8 * Real.sqrt 12) + 9 / 3 ^ 16) +
          A * (3 : ℝ) ^ (16 / 327680 : ℝ) / 900000) * C := by
    have hcenter := add_le_add hcenterOne (le_of_eq hcenterTwo)
    dsimp [C] at hcenter ⊢
    nlinarith [hmean, hcenter, htransport]
  have hnum := Numerics.AllOrder.cir_contraction
  have h1017 : (1017 / 1000 : ℝ) = 1.017 := by norm_num
  apply le_of_lt
  calc
    _ = (1.017 : ℝ) *
          (700 * γ + 144 * (900000 * γ) *
            (3 * Real.sqrt p / 3 ^ 8 + 9 * p / 3 ^ 16) +
            (107 / 12) * p * (9 / 2) * γ * 8 * (3 : ℝ) ^ (16 * γ) *
              (2.2 : ℝ) ^ 2 * 50) + γ := by rw [h1017]
    _ ≤ (1.017 : ℝ) *
          ((700 / (12 * 900000 : ℝ) +
            144 * (3 / (3 ^ 8 * Real.sqrt 12) + 9 / 3 ^ 16) +
            A * (3 : ℝ) ^ (16 / 327680 : ℝ) / 900000) * C) +
        (1 / (12 * 900000 : ℝ)) * C := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : ℝ) ≤ 1.017)) hadd
    _ = ((1.017 : ℝ) *
          (700 / (12 * 900000 : ℝ) +
            144 * (3 / (3 ^ 8 * Real.sqrt 12) + 9 / 3 ^ 16) +
            (107 / 12) * (9 / 2) * 8 * (2.2 : ℝ) ^ 2 * 50 *
              (3 : ℝ) ^ (16 / 327680 : ℝ) / 900000) +
        1 / (12 * 900000 : ℝ)) * C := by dsimp [A]; ring
    _ < (14 / 100 : ℝ) * C := by
      exact mul_lt_mul_of_pos_right (by simpa only [A] using hnum) hC
    _ = (14 / 100 : ℝ) * (900000 * γ * p) := by rfl

/-- For γ>γ*, the single native root20 bound covers every source even order
through P=20; this is the large-branch finite-even cap with actual MemLp data. -/
theorem aoCir_large_gamma_finite_even_caps (M : ABKModel 2) (h : ℝ)
    (hγ : (1 / 327680 : ℝ) < M.gamma) (hγ0 : M.gamma ≤ gammaZero)
    (m : ℤ) (hstate : nativeInductionState M h m) :
    smallGammaSeedP M.gamma = 20 ∧
      ∀ p : ℕ, 12 ≤ p → Even p → p ≤ smallGammaSeedP M.gamma →
        MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
            (Cutoff.cutoffSampleLaw M).toMeasure ∧
          lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
              (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
  have hseed := aoCir_large_gamma_native_seed M h hγ hγ0 m hstate
  have hrootState : root20 M m ≤ ENNReal.ofReal (2013 / 10000 * theta M) := hstate.2.2.1
  have hmem20 : MemLp (cutoffTraceDefect M m m) 20
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [Cold.coldNativeTrace, Int.natCast_zero, add_zero] using
      Cold.coldNativeTrace_zero_memLp hrootState
  refine ⟨hseed.1, ?_⟩
  intro p hp12 hpEven hpP
  have hp20 : p ≤ 20 := by simpa only [hseed.1] using hpP
  have hExp : (p : ℝ≥0∞) ≤ (20 : ℝ≥0∞) := by exact_mod_cast hp20
  have hmem : MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
      (Cutoff.cutoffSampleLaw M).toMeasure := hmem20.mono_exponent hExp
  have hmono : lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm (cutoffTraceDefect M m m) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    unfold lpNorm
    exact ENNReal.toReal_mono hmem20.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hExp)
  have hsource : (593 : ℝ) ≤ 900000 * (p : ℝ) := by
    have hp12R : (12 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp12
    nlinarith
  have hgammap : 593 * M.gamma ≤ 900000 * M.gamma * (p : ℝ) := by
    calc
      593 * M.gamma = M.gamma * 593 := by ring
      _ ≤ M.gamma * (900000 * (p : ℝ)) := mul_le_mul_of_nonneg_left hsource M.shellPrefix.gamma_pos.le
      _ = 900000 * M.gamma * (p : ℝ) := by ring
  refine ⟨hmem, ?_⟩
  exact hmono.trans (hseed.2.1.trans hgammap)

end ASDExplicitGamma.AllOrder
