/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.FiniteEven
public import ASDExplicitGamma.Cold.NativeCellIndex
public import ASDExplicitGamma.Cold.NativeFourColor

/-! # Finite-even averaging on the actual native depth-eight cells -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- Finite-moment symmetrization followed by four-color Minkowski.  Unequal
four-color populations are allowed; Cauchy-Schwarz pays their total by twice
the square root of the full population. -/
theorem four_color_finite_even_centered_average_lpNorm_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {X : ι → Ω → ℝ} {p : ℕ}
    (hpEven : Even p) (hpMin : 12 ≤ p) (color : ι → Fin 4)
    (hInd : ∀ c : Fin 4,
      iIndepFun (fun i : {i : ι // color i = c} => X i.val) μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, MemLp (X i) (p : ℝ≥0∞) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hCap : ∀ i q, 12 ≤ q → q ≤ p → Even q →
      lpNorm (X i) (q : ℝ≥0∞) μ ≤ C * q) :
    lpNorm (fun ω => (∑ i, (X i ω - μ[X i])) /
        (Fintype.card ι : ℝ)) (p : ℝ≥0∞) μ ≤
      144 * C * (3 * Real.sqrt ((p : ℝ) / Fintype.card ι) +
        9 * (p : ℝ) / Fintype.card ι) := by
  classical
  let Y : Fin 4 → Ω → ℝ := fun c ω =>
    ∑ i : {i : ι // color i = c}, (X i.val ω - μ[X i.val])
  have hterm : ∀ i, MemLp (fun ω => X i ω - μ[X i]) (p : ℝ≥0∞) μ := by
    intro i
    exact (hX i).sub (memLp_const (μ[X i]))
  have hY : ∀ c, MemLp (Y c) (p : ℝ≥0∞) μ := by
    intro c
    exact memLp_finsetSum Finset.univ (fun i _ => hterm i.val)
  have hclass : ∀ c : Fin 4,
      lpNorm (Y c) (p : ℝ≥0∞) μ ≤
        108 * C * (Real.sqrt ((p : ℝ) * Fintype.card {i : ι // color i = c}) + p) := by
    intro c
    have h := finite_even_centered_independent_sum_lpNorm_le
      (μ := μ) (X := fun i : {i : ι // color i = c} => X i.val)
      hpEven hpMin (hInd c) (fun i => hXm i.val) (fun i => hX i.val)
      hC (fun i q hq hqp he => hCap i.val q hq hqp he)
    simpa only [Y] using h
  have hfiber : (fun ω : Ω => ∑ c : Fin 4, Y c ω) =
      fun ω => ∑ i, (X i ω - μ[X i]) := by
    funext ω
    dsimp [Y]
    exact Fintype.sum_fiberwise color (fun i => X i ω - μ[X i])
  have hpENN : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by
    exact_mod_cast (show 1 ≤ p by omega)
  have hsumLp : lpNorm (fun ω : Ω => ∑ c : Fin 4, Y c ω)
      (p : ℝ≥0∞) μ ≤ ∑ c : Fin 4, lpNorm (Y c) (p : ℝ≥0∞) μ :=
    lpNorm_sum_le (s := Finset.univ) (fun c _ => hY c) hpENN
  let N : Fin 4 → ℕ := fun c => Fintype.card {i : ι // color i = c}
  have hcount : (∑ c : Fin 4, (N c : ℝ)) = (Fintype.card ι : ℝ) := by
    have h := Fintype.sum_fiberwise color (fun _ : ι => (1 : ℝ))
    simpa only [N, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  have hpop := Cold.four_color_population_bound N
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hrootFactor : ∀ c : Fin 4,
      Real.sqrt ((p : ℝ) * (N c : ℕ)) =
        Real.sqrt (p : ℝ) * Real.sqrt (N c : ℝ) := by
    intro c
    rw [Real.sqrt_mul hp0]
  have hpop' : (∑ c : Fin 4, Real.sqrt (N c : ℝ)) ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) := by
    simpa only [hcount] using hpop
  have hclassSumEq :
      (∑ c : Fin 4, 108 * C *
          (Real.sqrt ((p : ℝ) * (N c : ℕ)) + p)) =
        108 * C * (Real.sqrt (p : ℝ) *
          (∑ c : Fin 4, Real.sqrt (N c : ℝ)) + 4 * p) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib]
    have hfirst :
        (∑ c : Fin 4, Real.sqrt ((p : ℝ) * (N c : ℕ))) =
          Real.sqrt (p : ℝ) * (∑ c : Fin 4, Real.sqrt (N c : ℝ)) := by
      calc
        _ = ∑ c : Fin 4, Real.sqrt (p : ℝ) * Real.sqrt (N c : ℝ) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [hrootFactor]
        _ = _ := by rw [Finset.mul_sum]
    rw [hfirst]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  have hclassSum :
      (∑ c : Fin 4, 108 * C *
          (Real.sqrt ((p : ℝ) * (N c : ℕ)) + p)) ≤
        216 * C * Real.sqrt ((p : ℝ) * Fintype.card ι) + 432 * C * p := by
    calc
      _ = 108 * C * (Real.sqrt (p : ℝ) *
          (∑ c : Fin 4, Real.sqrt (N c : ℝ)) + 4 * p) := hclassSumEq
      _ ≤ 108 * C * (Real.sqrt (p : ℝ) *
          (2 * Real.sqrt (Fintype.card ι : ℝ)) + 4 * p) := by
        have hscaled : Real.sqrt (p : ℝ) *
            (∑ c : Fin 4, Real.sqrt (N c : ℝ)) ≤
              Real.sqrt (p : ℝ) * (2 * Real.sqrt (Fintype.card ι : ℝ)) :=
          mul_le_mul_of_nonneg_left hpop' (Real.sqrt_nonneg (p : ℝ))
        have hinside : Real.sqrt (p : ℝ) *
              (∑ c : Fin 4, Real.sqrt (N c : ℝ)) + 4 * p ≤
            Real.sqrt (p : ℝ) * (2 * Real.sqrt (Fintype.card ι : ℝ)) + 4 * p := by
          simpa [add_comm] using add_le_add_right hscaled (4 * p)
        exact mul_le_mul_of_nonneg_left hinside (mul_nonneg (by norm_num) hC)
      _ = 216 * C * Real.sqrt ((p : ℝ) * Fintype.card ι) + 432 * C * p := by
        calc
          _ = 216 * C * (Real.sqrt (p : ℝ) *
                Real.sqrt (Fintype.card ι : ℝ)) + 432 * C * p := by ring
          _ = _ := by
            have hprod : Real.sqrt (p : ℝ) * Real.sqrt (Fintype.card ι : ℝ) =
                Real.sqrt ((p : ℝ) * Fintype.card ι) :=
              (Real.sqrt_mul hp0 (Fintype.card ι : ℝ)).symm
            rw [hprod]
  have hNpos : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsumCentered :
      lpNorm (fun ω => ∑ i, (X i ω - μ[X i])) (p : ℝ≥0∞) μ ≤
        216 * C * Real.sqrt ((p : ℝ) * Fintype.card ι) + 432 * C * p := by
    rw [← hfiber]
    have hsumClassCap :
        (∑ c : Fin 4, lpNorm (Y c) (p : ℝ≥0∞) μ) ≤
          ∑ c : Fin 4, 108 * C *
            (Real.sqrt ((p : ℝ) * (N c : ℕ)) + p) :=
      Finset.sum_le_sum fun c _ => hclass c
    simpa only [N] using hsumLp.trans (hsumClassCap.trans hclassSum)
  rw [lpNorm_fun_div_natCast Fintype.card_ne_zero]
  have hnormalized :
      lpNorm (fun ω => ∑ i, (X i ω - μ[X i])) (p : ℝ≥0∞) μ /
          (Fintype.card ι : ℝ) ≤
        216 * C * Real.sqrt ((p : ℝ) / Fintype.card ι) +
          432 * C * (p : ℝ) / Fintype.card ι := by
    have hsqrt :
        Real.sqrt ((p : ℝ) * Fintype.card ι) / Fintype.card ι =
          Real.sqrt ((p : ℝ) / Fintype.card ι) := by
      calc
        Real.sqrt ((p : ℝ) * Fintype.card ι) / Fintype.card ι =
            (Real.sqrt (p : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) /
              Fintype.card ι := by rw [Real.sqrt_mul hp0]
        _ = Real.sqrt (p : ℝ) / Real.sqrt (Fintype.card ι : ℝ) := by
          have hsquare := Real.sq_sqrt hNpos.le
          have hrootN : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hNpos
          calc
            _ = Real.sqrt (p : ℝ) * Real.sqrt (Fintype.card ι : ℝ) /
                (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 := by
              congr 1
              exact hsquare.symm
            _ = _ := by field_simp [ne_of_gt hrootN]
        _ = Real.sqrt ((p : ℝ) / Fintype.card ι) := by
          rw [Real.sqrt_div hp0]
    calc
      _ ≤ (216 * C * Real.sqrt ((p : ℝ) * Fintype.card ι) + 432 * C * p) /
          (Fintype.card ι : ℝ) := div_le_div_of_nonneg_right hsumCentered hNpos.le
      _ = _ := by
        rw [add_div]
        have hfirst :
            216 * C * Real.sqrt ((p : ℝ) * Fintype.card ι) /
                Fintype.card ι =
              216 * C * Real.sqrt ((p : ℝ) / Fintype.card ι) := by
          calc
            _ = 216 * C * (Real.sqrt ((p : ℝ) * Fintype.card ι) /
                Fintype.card ι) := by ring
            _ = _ := by rw [hsqrt]
        rw [hfirst]
  have hC0 : 0 ≤ C := hC
  have hroot0 : 0 ≤ Real.sqrt ((p : ℝ) / Fintype.card ι) := Real.sqrt_nonneg _
  have hpdiv0 : 0 ≤ (p : ℝ) / Fintype.card ι := div_nonneg hp0 hNpos.le
  have htarget :
      216 * C * Real.sqrt ((p : ℝ) / Fintype.card ι) +
          432 * C * (p : ℝ) / Fintype.card ι ≤
        144 * C * (3 * Real.sqrt ((p : ℝ) / Fintype.card ι) +
          9 * (p : ℝ) / Fintype.card ι) := by
    calc
      _ ≤ 432 * C * Real.sqrt ((p : ℝ) / Fintype.card ι) +
          1296 * C * (p : ℝ) / Fintype.card ι := by
        have hrootCoef :
            216 * C * Real.sqrt ((p : ℝ) / Fintype.card ι) ≤
              432 * C * Real.sqrt ((p : ℝ) / Fintype.card ι) := by
          have hcoef : 0 ≤ 216 * C := mul_nonneg (by norm_num) hC0
          nlinarith [mul_nonneg hcoef hroot0]
        have hlinCoef : 432 * C * (p : ℝ) ≤ 1296 * C * (p : ℝ) := by
          nlinarith [mul_nonneg hC0 hp0]
        exact add_le_add hrootCoef (div_le_div_of_nonneg_right hlinCoef hNpos.le)
      _ = 144 * C * (3 * Real.sqrt ((p : ℝ) / Fintype.card ι) +
          9 * (p : ℝ) / Fintype.card ι) := by ring
  exact hnormalized.trans htarget

/-- The finite-even centered average of the actual depth-eight native child
traces.  Every child is a genuine descendant of the scale-`m+8` origin square,
has the source scale `m`, and inherits all even moment caps from the origin
trace by the exact translated-cell law. -/
theorem aoCir_native_child_average_centered_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {p : ℕ} (hpEven : Even p) (hpMin : 12 ≤ p)
    (hMoment : ∀ q : ℕ, 12 ≤ q → q ≤ p → Even q →
      MemLp (cutoffTraceDefect M m m) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M m m) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (q : ℝ)) :
    let Q : Fin (9 ^ 8) → TriadicCube 2 := fun i =>
      (Cold.coldNativeChildCell m 0 8 i)
    let X : Fin (9 ^ 8) → Cutoff.CutoffSample 2 → ℝ :=
      fun i => Cold.coldNativeCellTrace M m (Q i)
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    lpNorm (fun ω => (∑ i, (X i ω - μ[X i])) / (3 ^ 16 : ℝ))
        (p : ℝ≥0∞) μ ≤
      144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
          9 * (p : ℝ) / (3 ^ 16 : ℝ)) := by
  classical
  let Q : Fin (9 ^ 8) → TriadicCube 2 := fun i => Cold.coldNativeChildCell m 0 8 i
  let X : Fin (9 ^ 8) → Cutoff.CutoffSample 2 → ℝ := fun i =>
    Cold.coldNativeCellTrace M m (Q i)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hscale : ∀ i, (Q i).scale = m := by
    intro i
    simpa using Cold.coldNativeChildCell_scale (m := m) (k := 0) (ell := 8)
      (by norm_num) i
  have hQ : Function.Injective Q := by
    exact Cold.coldNativeChildCell_injective m 0 8
  have hInd : ∀ c : Fin 4,
      iIndepFun (fun i : {i : Fin (9 ^ 8) // Cold.coldCubeColor (Q i) = c} =>
        X i.val) μ := by
    exact Cold.cold_native_trace_four_color M h hM m m (by omega) Q hQ hscale
  have hXm : ∀ i, Measurable (X i) := by
    intro i
    exact Cold.coldNativeCellTrace_measurable M m (Q i)
  have hX : ∀ i, MemLp (X i) (p : ℝ≥0∞) μ := by
    intro i
    have h := hMoment p hpMin (by omega) hpEven
    have hscalei : (Q i).scale = m := hscale i
    have horigin : MemLp (cutoffTraceDefect M m (Q i).scale)
        (p : ℝ≥0∞) μ := by simpa only [hscalei] using h.1
    exact (Cold.coldNativeCellTrace_memLp_iff M m (Q i) (p : ℝ≥0∞)).2 horigin
  have hCap : ∀ i q, 12 ≤ q → q ≤ p → Even q →
      lpNorm (X i) (q : ℝ≥0∞) μ ≤ 900000 * M.gamma * (q : ℝ) := by
    intro i q hq hqp heven
    have h := hMoment q hq hqp heven
    calc
      lpNorm (X i) (q : ℝ≥0∞) μ =
          lpNorm (cutoffTraceDefect M m (Q i).scale) (q : ℝ≥0∞) μ :=
        Cold.coldNativeCellTrace_norm M m (Q i) (q : ℝ≥0∞)
      _ ≤ 900000 * M.gamma * (q : ℝ) := by
        simpa only [hscale i] using h.2
  have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hC : 0 ≤ (900000 : ℝ) * M.gamma := by positivity
  have hAvg := four_color_finite_even_centered_average_lpNorm_le
    (μ := μ) (X := X) hpEven hpMin (fun i => Cold.coldCubeColor (Q i))
    hInd hXm hX hC hCap
  have hcard : Fintype.card (Fin (9 ^ 8)) = 3 ^ 16 := by norm_num
  norm_num [Q, X, μ, hcard] at hAvg ⊢
  exact hAvg

end ASDExplicitGamma.AllOrder
