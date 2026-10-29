/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationMaxima
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Gaussian concentration for countable suprema

Countable families of linear forms on one common finite-dimensional standard Gaussian space are
handled by increasing finite maxima and continuity of measure from below.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The pointwise supremum of a countable family of centered Gaussian linear forms. -/
noncomputable def gaussianCountableSup {n : ℕ}
    (a : ℕ → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ⨆ k, gaussianFiniteLinearForm (a k) x

private noncomputable def gaussianCountablePrefixMaximum {n : ℕ}
    (a : ℕ → Fin n → ℝ) (N : ℕ) (x : Fin n → ℝ) : ℝ :=
  gaussianFiniteMaximum (Nat.succ_pos N) (fun i : Fin (N + 1) => a i.val) x

private theorem gaussianCountableLinearForm_abs_le {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) (k : ℕ) (x : Fin n → ℝ) :
    |gaussianFiniteLinearForm (a k) x| ≤ (n : ℝ) * L * ‖x‖ := by
  have h := gaussianFiniteLinearForm_abs_le
    (a := fun _ : Fin 1 => a k)
    (hcoeff := fun _ => hcoeff k) ⟨0, by omega⟩ x
  simpa [gaussianFiniteLinearForm] using h

private theorem gaussianCountablePrefix_le_sup {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) (N : ℕ) (x : Fin n → ℝ) :
    gaussianCountablePrefixMaximum a N x ≤ gaussianCountableSup a x := by
  classical
  unfold gaussianCountablePrefixMaximum gaussianFiniteMaximum
  change (Finset.univ : Finset (Fin (N + 1))).sup' (by simp)
      (fun i => gaussianFiniteLinearForm (a i.val) x) ≤
    sSup (Set.range fun k : ℕ => gaussianFiniteLinearForm (a k) x)
  apply Finset.sup'_le
  intro i hi
  let C : ℝ := (n : ℝ) * L * ‖x‖
  have hbdd : BddAbove (Set.range fun k : ℕ => gaussianFiniteLinearForm (a k) x) := by
    refine ⟨C, ?_⟩
    rintro y ⟨k, rfl⟩
    exact (abs_le.mp (gaussianCountableLinearForm_abs_le a hcoeff k x)).2
  exact le_csSup hbdd (Set.mem_range_self i.val)

private theorem gaussianCountablePrefix_mono {n : ℕ}
    (a : ℕ → Fin n → ℝ) (N : ℕ) (x : Fin n → ℝ) :
    gaussianCountablePrefixMaximum a N x ≤ gaussianCountablePrefixMaximum a (N + 1) x := by
  classical
  unfold gaussianCountablePrefixMaximum gaussianFiniteMaximum
  change (Finset.univ : Finset (Fin (N + 1))).sup' (by simp)
      (fun i => gaussianFiniteLinearForm (a i.val) x) ≤
    (Finset.univ : Finset (Fin (N + 2))).sup' (by simp)
      (fun j => gaussianFiniteLinearForm (a j.val) x)
  apply Finset.sup'_le
  intro i hi
  let j : Fin (N + 2) := ⟨i.val, by omega⟩
  have hj : gaussianFiniteLinearForm (a i.val) x ≤
      (Finset.univ : Finset (Fin (N + 2))).sup' (by simp)
        (fun j : Fin (N + 2) => gaussianFiniteLinearForm (a j.val) x) := by
    exact Finset.le_sup' (f := fun j : Fin (N + 2) =>
      gaussianFiniteLinearForm (a j.val) x) (Finset.mem_univ j)
  simpa [j] using hj

private theorem gaussianCountableSup_abs_le {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) (x : Fin n → ℝ) :
    |gaussianCountableSup a x| ≤ (n : ℝ) * L * ‖x‖ := by
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a 0))).trans (hcoeff 0)
  have hbound (k : ℕ) :
      |gaussianFiniteLinearForm (a k) x| ≤ (n : ℝ) * L * ‖x‖ :=
    gaussianCountableLinearForm_abs_le a hcoeff k x
  change |sSup (Set.range fun k : ℕ => gaussianFiniteLinearForm (a k) x)| ≤
    (n : ℝ) * L * ‖x‖
  apply abs_le.mpr
  constructor
  · have hzero := (abs_le.mp (hbound 0)).1
    have hbdd : BddAbove (Set.range fun k : ℕ => gaussianFiniteLinearForm (a k) x) := by
      refine ⟨(n : ℝ) * L * ‖x‖, ?_⟩
      rintro y ⟨k, rfl⟩
      exact (abs_le.mp (hbound k)).2
    exact le_trans hzero (le_csSup hbdd (Set.mem_range_self 0))
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨k, rfl⟩
    exact (abs_le.mp (hbound k)).2

private theorem continuous_gaussianFiniteLinearForm_countable {n : ℕ}
    (a : Fin n → ℝ) : Continuous (gaussianFiniteLinearForm a) := by
  unfold gaussianFiniteLinearForm
  fun_prop

private theorem tendsto_gaussianCountablePrefixMaximum {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) (x : Fin n → ℝ) :
    Tendsto (fun N => gaussianCountablePrefixMaximum a N x) atTop
      (𝓝 (gaussianCountableSup a x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    change b < sSup (Set.range fun k : ℕ => gaussianFiniteLinearForm (a k) x) at hb
    let C : ℝ := (n : ℝ) * L * ‖x‖
    have hbdd : BddAbove (Set.range fun k : ℕ => gaussianFiniteLinearForm (a k) x) := by
      refine ⟨C, ?_⟩
      rintro y ⟨k, rfl⟩
      exact (abs_le.mp (gaussianCountableLinearForm_abs_le a hcoeff k x)).2
    obtain ⟨y, ⟨k, rfl⟩, hk⟩ := (lt_csSup_iff hbdd (Set.range_nonempty _)).mp hb
    filter_upwards [eventually_ge_atTop k] with N hN
    let hi : Fin (N + 1) := ⟨k, by omega⟩
    have hterm : gaussianFiniteLinearForm (a k) x ≤
        gaussianCountablePrefixMaximum a N x := by
      unfold gaussianCountablePrefixMaximum gaussianFiniteMaximum
      change gaussianFiniteLinearForm (a k) x ≤
        (Finset.univ : Finset (Fin (N + 1))).sup' (by simp)
          (fun i => gaussianFiniteLinearForm (a i.val) x)
      have hterm' : gaussianFiniteLinearForm (a hi.val) x ≤
          (Finset.univ : Finset (Fin (N + 1))).sup' (by simp)
            (fun i : Fin (N + 1) => gaussianFiniteLinearForm (a i.val) x) :=
        Finset.le_sup' (f := fun i : Fin (N + 1) =>
          gaussianFiniteLinearForm (a i.val) x) (Finset.mem_univ hi)
      have hval : hi.val = k := by simp [hi]
      rw [hval] at hterm'
      exact hterm'
    exact lt_of_lt_of_le hk (by simpa using hterm)
  · intro b hb
    filter_upwards with N
    exact lt_of_le_of_lt (gaussianCountablePrefix_le_sup a hcoeff N x) hb

private theorem measurable_gaussianCountableSup {n : ℕ}
    (a : ℕ → Fin n → ℝ) : Measurable (gaussianCountableSup a) := by
  change Measurable (fun x => ⨆ k, gaussianFiniteLinearForm (a k) x)
  apply Measurable.iSup
  intro k
  exact (continuous_gaussianFiniteLinearForm_countable (a k)).measurable

private theorem integrable_gaussianCountableSup {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) :
    Integrable (gaussianCountableSup a) (standardGaussianPi n) := by
  let C : ℝ := (n : ℝ) * L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply integrable_of_pi_polynomial_bound (measurable_gaussianCountableSup a)
    (C := C) hC (d := 1)
  intro x
  calc
    |gaussianCountableSup a x| ≤ C * ‖x‖ := by
      simpa [C, mul_assoc] using gaussianCountableSup_abs_le a hcoeff x
    _ ≤ C * (1 + ‖x‖) := by
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hC
    _ = C * (1 + ‖x‖) ^ 1 := by rw [pow_one]

private theorem gaussianCountablePrefix_abs_le {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) (N : ℕ) (x : Fin n → ℝ) :
    |gaussianCountablePrefixMaximum a N x| ≤ (n : ℝ) * L * ‖x‖ := by
  have hbound (k : ℕ) :
      |gaussianFiniteLinearForm (a k) x| ≤ (n : ℝ) * L * ‖x‖ :=
    gaussianCountableLinearForm_abs_le a hcoeff k x
  have hupper : gaussianCountablePrefixMaximum a N x ≤ (n : ℝ) * L * ‖x‖ := by
    unfold gaussianCountablePrefixMaximum gaussianFiniteMaximum
    apply Finset.sup'_le
    intro i hi
    exact (abs_le.mp (hbound i.val)).2
  have hlower : -( (n : ℝ) * L * ‖x‖) ≤ gaussianCountablePrefixMaximum a N x := by
    have hterm : gaussianFiniteLinearForm (a 0) x ≤
        gaussianCountablePrefixMaximum a N x := by
      unfold gaussianCountablePrefixMaximum gaussianFiniteMaximum
      exact Finset.le_sup' (f := fun i : Fin (N + 1) =>
        gaussianFiniteLinearForm (a i.val) x) (Finset.mem_univ ⟨0, by omega⟩)
    exact le_trans (abs_le.mp (hbound 0)).1 hterm
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The expectations of increasing finite maxima converge to the expectation of the countable
supremum. The finite-dimensional linear-growth envelope is integrable under the product Gaussian. -/
private theorem tendsto_gaussianCountablePrefixMean {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) :
    Tendsto (fun N => ∫ x, gaussianCountablePrefixMaximum a N x ∂(standardGaussianPi n))
      atTop (𝓝 (∫ x, gaussianCountableSup a x ∂(standardGaussianPi n))) := by
  let C : ℝ := (n : ℝ) * L
  let R : (Fin n → ℝ) → ℝ := fun x => C * (1 + ‖x‖)
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a 0))).trans (hcoeff 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hRmeas : Measurable R := by
    dsimp [R]
    fun_prop
  have hRInt : Integrable R (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound hRmeas (C := C) hC (d := 1)
    intro x
    change |C * (1 + ‖x‖)| ≤ C * (1 + ‖x‖) ^ 1
    have hnonneg : 0 ≤ C * (1 + ‖x‖) :=
      mul_nonneg hC (show 0 ≤ 1 + ‖x‖ by positivity)
    rw [pow_one, abs_of_nonneg hnonneg]
  have hMInt (N : ℕ) :
      Integrable (gaussianCountablePrefixMaximum a N) (standardGaussianPi n) := by
    let aN : Fin (N + 1) → Fin n → ℝ := fun i => a i.val
    exact (integral_exp_centered_le_of_gaussianFiniteMaximum
      (Nat.succ_pos N) aN (L := L) (lam := 0) (fun i => hcoeff i.val)).1
  apply tendsto_integral_filter_of_dominated_convergence
    (F := gaussianCountablePrefixMaximum a) (f := gaussianCountableSup a) (bound := R)
  · exact Eventually.of_forall fun N => (hMInt N).aestronglyMeasurable
  · filter_upwards with N
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      calc
        |gaussianCountablePrefixMaximum a N x| ≤ (n : ℝ) * L * ‖x‖ :=
          gaussianCountablePrefix_abs_le a hcoeff N x
        _ = C * ‖x‖ := by simp [C, mul_assoc]
        _ ≤ C * (1 + ‖x‖) := mul_le_mul_of_nonneg_left
          (by linarith [norm_nonneg x]) hC
  · exact hRInt
  · exact ae_of_all _ fun x => tendsto_gaussianCountablePrefixMaximum a hcoeff x

private theorem gaussianCountableSup_tail_below {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L s t : ℝ} (hL : 0 < L) (hs : 0 ≤ s) (hst : s < t)
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) :
    (standardGaussianPi n).real {x | t ≤ gaussianCountableSup a x -
      ∫ y, gaussianCountableSup a y ∂(standardGaussianPi n)} ≤
      Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
  let m : ℝ := ∫ y, gaussianCountableSup a y ∂(standardGaussianPi n)
  let M : ℕ → (Fin n → ℝ) → ℝ := gaussianCountablePrefixMaximum a
  let mN : ℕ → ℝ := fun N => ∫ y, M N y ∂(standardGaussianPi n)
  let E : ℕ → Set (Fin n → ℝ) := fun N => {x | s ≤ M N x - m}
  have hMInt (N : ℕ) : Integrable (M N) (standardGaussianPi n) := by
    let aN : Fin (N + 1) → Fin n → ℝ := fun i => a i.val
    have h := integral_exp_centered_le_of_gaussianFiniteMaximum
      (Nat.succ_pos N) aN (L := L) (lam := 0) (fun i => hcoeff i.val)
    change Integrable (gaussianFiniteMaximum (Nat.succ_pos N)
      (fun i : Fin (N + 1) => a i.val)) (standardGaussianPi n)
    exact h.1
  have hmeans : Tendsto mN atTop (𝓝 m) := by
    simpa [mN, m, M] using tendsto_gaussianCountablePrefixMean a hcoeff
  have hmeanMono : Monotone mN := by
    intro N K hNK
    have hpoint : ∀ x, M N x ≤ M K x := by
      intro x
      induction hNK with
      | refl => exact le_rfl
      | @step K hNK ih =>
          exact le_trans ih (by simpa [M] using gaussianCountablePrefix_mono a K x)
    apply integral_mono_ae (hMInt N) (hMInt K)
    exact ae_of_all _ hpoint
  have hmint (N : ℕ) : mN N ≤ m := by
    have hev : ∀ᶠ K in atTop, mN N ≤ mN K := by
      filter_upwards [eventually_ge_atTop N] with K hNK
      exact hmeanMono hNK
    exact ge_of_tendsto hmeans hev
  have hmono : Monotone E := by
    intro N K hNK x hx
    have hprefix : M N x ≤ M K x := by
      induction hNK with
      | refl => exact le_rfl
      | @step K hNK ih =>
          exact le_trans ih (by
            simpa [M] using gaussianCountablePrefix_mono a K x)
    exact hx.trans (sub_le_sub_right hprefix m)
  have hfinite (N : ℕ) :
      (standardGaussianPi n).real
        {x | s ≤ M N x - mN N} ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
    let aN : Fin (N + 1) → Fin n → ℝ := fun i => a i.val
    have h := measure_centered_tail_le_of_gaussianFiniteMaximum
      (Nat.succ_pos N) aN hL hs (fun i => hcoeff i.val)
    simpa [M, mN, gaussianCountablePrefixMaximum, aN] using h.1
  have hEbound (N : ℕ) :
      (standardGaussianPi n).real (E N) ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
    have hsubset : E N ⊆ {x | s ≤ M N x - mN N} := by
      intro x hx
      change s ≤ M N x - m at hx
      change s ≤ M N x - mN N
      have hshift : M N x - m ≤ M N x - mN N := by linarith [hmint N]
      exact le_trans hx hshift
    exact (measureReal_mono hsubset).trans (hfinite N)
  have hUnionBound :
      (standardGaussianPi n).real (⋃ N, E N) ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
    let μ := standardGaussianPi n
    let B := Real.exp (-s ^ 2 / (2 * L ^ 2))
    have hB : 0 ≤ B := Real.exp_nonneg _
    have hmeasure (N : ℕ) : μ (E N) ≤ ENNReal.ofReal B := by
      rw [← ofReal_measureReal (μ := μ) (s := E N) (by finiteness)]
      exact ENNReal.ofReal_le_ofReal (by simpa [B] using hEbound N)
    have hlim : Tendsto (fun N => μ (E N)) atTop (𝓝 (μ (⋃ N, E N))) := by
      exact tendsto_measure_iUnion_atTop hmono
    have hle := le_of_tendsto hlim (Eventually.of_forall hmeasure)
    change (μ (⋃ N, E N)).toReal ≤ B
    calc
      (μ (⋃ N, E N)).toReal ≤ (ENNReal.ofReal B).toReal :=
        ENNReal.toReal_mono (by simp) hle
      _ = B := ENNReal.toReal_ofReal hB
  have hsubsetUnion :
      {x | t ≤ gaussianCountableSup a x - m} ⊆ ⋃ N, E N := by
    intro x hx
    have hstx : s + m < gaussianCountableSup a x := by
      have h := hx
      dsimp [m] at h
      linarith
    have hev := (tendsto_order.mp
      (tendsto_gaussianCountablePrefixMaximum a hcoeff x)).1
      (s + m) hstx
    obtain ⟨N, hN⟩ := hev.exists
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    change s ≤ M N x - m
    have hN' : s + m < M N x := by simpa [M] using hN
    linarith
  calc
    (standardGaussianPi n).real {x | t ≤ gaussianCountableSup a x - m} ≤
        (standardGaussianPi n).real (⋃ N, E N) := measureReal_mono hsubsetUnion
    _ ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by simpa [m] using hUnionBound

/-- A countable family of centered Gaussian linear forms on one common finite-dimensional
standard Gaussian space has the sharp upper tail bound. The coefficient norm bound `L` is the
common standard-deviation bound, and the countable supremum is integrable by the proved linear
growth estimate. The proof passes from increasing finite maxima by continuity of measure from
below. -/
theorem measure_centered_tail_le_of_gaussianCountableSup {n : ℕ}
    (a : ℕ → Fin n → ℝ) {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hcoeff : ∀ k, ‖WithLp.toLp 2 (a k)‖ ≤ L) :
    Integrable (gaussianCountableSup a) (standardGaussianPi n) ∧
      (standardGaussianPi n).real {x | t ≤ gaussianCountableSup a x -
        ∫ y, gaussianCountableSup a y ∂(standardGaussianPi n)} ≤
        Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  refine ⟨integrable_gaussianCountableSup a hL.le hcoeff, ?_⟩
  by_cases ht0 : t = 0
  · subst t
    calc
      (standardGaussianPi n).real {x | 0 ≤ gaussianCountableSup a x -
          ∫ y, gaussianCountableSup a y ∂(standardGaussianPi n)} ≤
          (standardGaussianPi n).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp [standardGaussianPi]
      _ = Real.exp (-(0 : ℝ) ^ 2 / (2 * L ^ 2)) := by simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let u : ℕ → ℝ := fun N => t * (1 - ((N : ℝ) + 1)⁻¹)
    have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hden : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [hnat.eventually (eventually_ge_atTop (b - 1))] with N hN
      change b ≤ (N : ℝ) + 1
      linarith
    have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    have hu : Tendsto u atTop (𝓝 t) := by
      have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have hfactor := hconst.sub hinv
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).mul hfactor
      simpa [u] using h
    have harg : Tendsto (fun N => -(u N) ^ 2 / (2 * L ^ 2)) atTop
        (𝓝 (-t ^ 2 / (2 * L ^ 2))) := by
      have hsq := hu.pow 2
      have hneg := hsq.neg
      simpa using hneg.div_const (2 * L ^ 2)
    have hexp : Tendsto (fun N => Real.exp (-(u N) ^ 2 / (2 * L ^ 2))) atTop
        (𝓝 (Real.exp (-t ^ 2 / (2 * L ^ 2)))) := by
      exact Real.continuous_exp.continuousAt.tendsto.comp harg
    have hbound (N : ℕ) :
        (standardGaussianPi n).real {x | t ≤ gaussianCountableSup a x -
          ∫ y, gaussianCountableSup a y ∂(standardGaussianPi n)} ≤
          Real.exp (-(u N) ^ 2 / (2 * L ^ 2)) := by
      have hd : ((N : ℝ) + 1)⁻¹ > 0 := inv_pos.mpr (by positivity)
      have hdle : ((N : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [inv_eq_one_div]
        apply (div_le_one (by positivity)).2
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
      have hu0 : 0 ≤ u N := by
        dsimp [u]
        exact mul_nonneg ht (by linarith)
      have hut : u N < t := by
        dsimp [u]
        have hfactor : 1 - ((N : ℝ) + 1)⁻¹ < 1 := by linarith
        nlinarith [mul_lt_mul_of_pos_left hfactor htpos]
      exact gaussianCountableSup_tail_below a hL hu0 hut hcoeff
    have hfinal := ge_of_tendsto hexp (Eventually.of_forall hbound)
    simpa using hfinal

end ASDExplicitGamma.Gaussian
