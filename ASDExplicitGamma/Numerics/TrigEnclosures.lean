module

public import ASDExplicitGamma.Numerics.Enclosures
public import ASDExplicitGamma.Numerics.QInterval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating Taylor enclosures for sine and cosine

The partial sums are rational polynomials in the input. On `[0, π/2]`, each
remainder is bounded by the first omitted term, so their rational evaluations
can be combined with an interval for `π`.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics

open Filter Nat
open scoped Topology

/-- Absolute size of the `n`th sine-series term. -/
noncomputable def sinTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)

/-- Absolute size of the `n`th cosine-series term. -/
noncomputable def cosTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / ((2 * n).factorial : ℝ)

/-- The cosine series with its first term removed, reindexed from zero. -/
noncomputable def cosTailTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ)

/-- The first `n` terms of the alternating sine series. -/
noncomputable def sinTaylor (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * sinTerm x i

/-- The first `n` terms of the alternating cosine series. -/
noncomputable def cosTaylor (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * cosTerm x i

private theorem sinTerm_step {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (n : ℕ) :
    sinTerm x (n + 1) ≤ sinTerm x n := by
  have hx2sq : x ^ 2 ≤ 4 := by nlinarith
  have hden : (0 : ℝ) < ((2 * n + 3) : ℝ) * (2 * n + 2) := by positivity
  have hratio : x ^ 2 / (((2 * n + 3 : ℝ) * (2 * n + 2))) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith
  have heq : sinTerm x (n + 1) = sinTerm x n *
      (x ^ 2 / (((2 * n + 3 : ℝ) * (2 * n + 2)))) := by
    unfold sinTerm
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [heq]
  have hterm : 0 ≤ sinTerm x n := by
    unfold sinTerm
    exact div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)
  calc sinTerm x n * (x ^ 2 / ((2 * n + 3 : ℝ) * (2 * n + 2)))
      ≤ sinTerm x n * 1 := mul_le_mul_of_nonneg_left hratio hterm
    _ = sinTerm x n := mul_one _

private theorem cosTailTerm_step {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (n : ℕ) :
    cosTailTerm x (n + 1) ≤ cosTailTerm x n := by
  have hx2sq : x ^ 2 ≤ 4 := by nlinarith
  have hden : (0 : ℝ) < ((2 * n + 4) : ℝ) * (2 * n + 3) := by positivity
  have hratio : x ^ 2 / (((2 * n + 4 : ℝ) * (2 * n + 3))) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith
  have heq : cosTailTerm x (n + 1) = cosTailTerm x n *
      (x ^ 2 / (((2 * n + 4 : ℝ) * (2 * n + 3)))) := by
    unfold cosTailTerm
    rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by omega, pow_add,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [heq]
  have hterm : 0 ≤ cosTailTerm x n := by
    unfold cosTailTerm
    exact div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)
  calc cosTailTerm x n * (x ^ 2 / ((2 * n + 4 : ℝ) * (2 * n + 3)))
      ≤ cosTailTerm x n * 1 := mul_le_mul_of_nonneg_left hratio hterm
    _ = cosTailTerm x n := mul_one _

private theorem sinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    Antitone (sinTerm x) := antitone_nat_of_succ_le (sinTerm_step hx0 hx2)

private theorem cosTailTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    Antitone (cosTailTerm x) := antitone_nat_of_succ_le (cosTailTerm_step hx0 hx2)

private def altPartial (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i

private theorem alternatingTaylor_error {f : ℕ → ℝ} {l : ℝ}
    (hfl : Tendsto (fun n => altPartial f n) atTop (𝓝 l)) (hfa : Antitone f)
    (n : ℕ) (hn : 0 ≤ f n) : |l - altPartial f n| ≤ f n := by
  obtain he | ho := even_or_odd n
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp he
    have heven : altPartial f (2 * k) ≤ l := hfa.alternating_series_le_tendsto hfl k
    have hodd : l ≤ altPartial f (2 * k + 1) := hfa.tendsto_le_alternating_series hfl k
    have hstep : altPartial f (2 * k + 1) = altPartial f (2 * k) + f (2 * k) := by
      unfold altPartial
      rw [Finset.sum_range_succ]
      simp
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp ho
    have hodd : l ≤ altPartial f (2 * k + 1) := hfa.tendsto_le_alternating_series hfl k
    have heven : altPartial f (2 * (k + 1)) ≤ l := hfa.alternating_series_le_tendsto hfl (k + 1)
    have hstep : altPartial f (2 * (k + 1)) = altPartial f (2 * k + 1) - f (2 * k + 1) := by
      unfold altPartial
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Finset.sum_range_succ]
      simp [pow_succ, sub_eq_add_neg]
    rw [abs_le]
    constructor <;> linarith

/-- The sine Taylor polynomial has a first-omitted-term remainder on `[0,2]`. -/
theorem sinTaylor_error {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (n : ℕ) :
    |Real.sin x - sinTaylor x n| ≤ sinTerm x n := by
  have hfl : Tendsto (fun n => altPartial (sinTerm x) n) atTop (𝓝 (Real.sin x)) := by
    simpa [altPartial, sinTerm, mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  simpa [sinTaylor, altPartial] using
    alternatingTaylor_error hfl (sinTerm_antitone hx0 hx2) n
      (div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))

private theorem cosTaylor_split {x : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    cosTaylor x n = 1 - altPartial (cosTailTerm x) (n - 1) := by
  unfold cosTaylor altPartial
  rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ']
  have hterm : ∀ i, (-1 : ℝ) ^ (i + 1) * cosTerm x (i + 1) =
      -((-1 : ℝ) ^ i * cosTailTerm x i) := by
    intro i
    have he : 2 * (i + 1) = 2 * i + 2 := by omega
    simp [cosTerm, cosTailTerm, pow_succ, he]
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  norm_num [cosTerm]
  ring

/-- The cosine Taylor polynomial has a first-omitted-term remainder on `[0,2]`.
The index is required to be at least two so the decreasing alternating tail starts after
its initial constant term. -/
theorem cosTaylor_error {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) {n : ℕ} (hn : 2 ≤ n) :
    |Real.cos x - cosTaylor x n| ≤ cosTailTerm x (n - 1) := by
  have hcos : HasSum (fun i => (-1 : ℝ) ^ i * cosTerm x i) (Real.cos x) := by
    simpa [cosTerm, mul_div_assoc] using Real.hasSum_cos x
  have hsum := hcos.summable.sum_add_tsum_nat_add 1
  have hshift : Summable (fun i => (-1 : ℝ) ^ i * cosTailTerm x i) := by
    have hshift' : Summable (fun i => (-1 : ℝ) ^ (i + 1) * cosTerm x (i + 1)) :=
      (summable_nat_add_iff (f := fun i => (-1 : ℝ) ^ i * cosTerm x i) 1).mpr hcos.summable
    refine hshift'.neg.congr fun i => ?_
    have he : 2 * (i + 1) = 2 * i + 2 := by omega
    simp [cosTerm, cosTailTerm, pow_succ, he]
  have htail : (∑' i, (-1 : ℝ) ^ i * cosTailTerm x i) = 1 - Real.cos x := by
    have hrel : ∀ i, (-1 : ℝ) ^ (i + 1) * cosTerm x (i + 1) =
        -((-1 : ℝ) ^ i * cosTailTerm x i) := by
      intro i
      have he : 2 * (i + 1) = 2 * i + 2 := by omega
      simp [cosTerm, cosTailTerm, pow_succ, he]
    have hsumshift : (∑' i, (-1 : ℝ) ^ (i + 1) * cosTerm x (i + 1)) =
        -(∑' i, (-1 : ℝ) ^ i * cosTailTerm x i) := by
      calc
        _ = ∑' i, -((-1 : ℝ) ^ i * cosTailTerm x i) := tsum_congr hrel
        _ = _ := tsum_neg
    have hfirst : (∑ i ∈ Finset.range 1, (-1 : ℝ) ^ i * cosTerm x i) = 1 := by
      norm_num [cosTerm]
    have hdecomp := hsum
    rw [hcos.tsum_eq] at hdecomp
    rw [hfirst, hsumshift] at hdecomp
    linarith
  have hfl : Tendsto (fun n => altPartial (cosTailTerm x) n)
      atTop (𝓝 (1 - Real.cos x)) := by
    have ht := hshift.hasSum.tendsto_sum_nat
    rw [htail] at ht
    simpa [altPartial] using ht
  have herr := alternatingTaylor_error hfl (cosTailTerm_antitone hx0 hx2) (n - 1)
    (div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
  rw [cosTaylor_split (by omega)]
  calc abs (Real.cos x - (1 - altPartial (cosTailTerm x) (n - 1))) =
      abs (-((1 - Real.cos x) - altPartial (cosTailTerm x) (n - 1))) := by
        congr 1
        ring
    _ = abs ((1 - Real.cos x) - altPartial (cosTailTerm x) (n - 1)) := abs_neg _
    _ ≤ cosTailTerm x (n - 1) := herr

/-- Rational expression for a natural power. -/
def qexprPow (x : QExpr) : ℕ → QExpr
  | 0 => .const 1
  | n + 1 => .mul (qexprPow x n) x

/-- Rational expression for the sine Taylor polynomial. -/
def sinTaylorExpr (x : QExpr) : ℕ → QExpr
  | 0 => .const 0
  | n + 1 => .add (sinTaylorExpr x n)
      (.div (.mul (.const ((-1 : ℚ) ^ n)) (qexprPow x (2 * n + 1)))
        (.const ((2 * n + 1).factorial)))

/-- Rational expression for the cosine Taylor polynomial. -/
def cosTaylorExpr (x : QExpr) : ℕ → QExpr
  | 0 => .const 0
  | n + 1 => .add (cosTaylorExpr x n)
      (.div (.mul (.const ((-1 : ℚ) ^ n)) (qexprPow x (2 * n)))
        (.const ((2 * n).factorial)))

/-- Rational expression for a sine first-omitted-term bound. -/
def sinTermExpr (x : QExpr) (n : ℕ) : QExpr :=
  .div (qexprPow x (2 * n + 1)) (.const ((2 * n + 1).factorial))

/-- Rational expression for a cosine first-omitted-term bound. -/
def cosTailTermExpr (x : QExpr) (n : ℕ) : QExpr :=
  .div (qexprPow x (2 * n + 2)) (.const ((2 * n + 2).factorial))

private theorem evalQExprReal_qexprPow (env : ℕ → ℝ) (x : QExpr) (n : ℕ) :
    evalQExprReal env (qexprPow x n) = evalQExprReal env x ^ n := by
  induction n with
  | zero => simp [qexprPow, evalQExprReal]
  | succ n ih => simp [qexprPow, evalQExprReal, ih, pow_succ]

theorem evalQExprReal_sinTaylorExpr (env : ℕ → ℝ) (x : QExpr) (n : ℕ) :
    evalQExprReal env (sinTaylorExpr x n) = sinTaylor (evalQExprReal env x) n := by
  induction n with
  | zero => simp [sinTaylorExpr, evalQExprReal, sinTaylor]
  | succ n ih =>
      simp [sinTaylorExpr, evalQExprReal, evalQExprReal_qexprPow, ih,
        sinTaylor, sinTerm, mul_div_assoc, Finset.sum_range_succ]

theorem evalQExprReal_cosTaylorExpr (env : ℕ → ℝ) (x : QExpr) (n : ℕ) :
    evalQExprReal env (cosTaylorExpr x n) = cosTaylor (evalQExprReal env x) n := by
  induction n with
  | zero => simp [cosTaylorExpr, evalQExprReal, cosTaylor]
  | succ n ih =>
      simp [cosTaylorExpr, evalQExprReal, evalQExprReal_qexprPow, ih,
        cosTaylor, cosTerm, mul_div_assoc, Finset.sum_range_succ]

theorem evalQExprReal_sinTermExpr (env : ℕ → ℝ) (x : QExpr) (n : ℕ) :
    evalQExprReal env (sinTermExpr x n) = sinTerm (evalQExprReal env x) n := by
  simp [sinTermExpr, evalQExprReal, evalQExprReal_qexprPow, sinTerm]

theorem evalQExprReal_cosTailTermExpr (env : ℕ → ℝ) (x : QExpr) (n : ℕ) :
    evalQExprReal env (cosTailTermExpr x n) = cosTailTerm (evalQExprReal env x) n := by
  simp [cosTailTermExpr, evalQExprReal, evalQExprReal_qexprPow, cosTailTerm]

/-- Expand a Taylor-polynomial interval by the first-omitted-term radius. -/
def expandByError (p e : QInterval) : QInterval :=
  let r := max 0 e.hi
  ⟨p.lo - r, p.hi + r, by
    have hr : 0 ≤ r := le_max_left 0 e.hi
    linarith [p.valid]⟩

/-- The π argument used in rational trigonometric certificates. -/
def rationalPiExpr (r : ℚ) : QExpr := .mul (.const r) (.var 0)

def rationalPiIntervalEnv (piI : QInterval) : ℕ → QInterval := fun _ => piI
noncomputable def rationalPiRealEnv : ℕ → ℝ := fun _ => Real.pi

/-- Sine Taylor remainder for rational multiples of `π` in `[0,π/2]`. -/
theorem sin_rational_pi_taylor_error {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (n : ℕ) :
    |Real.sin ((r : ℝ) * Real.pi) - sinTaylor ((r : ℝ) * Real.pi) n| ≤
      sinTerm ((r : ℝ) * Real.pi) n := by
  have hr0R : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1R : (r : ℝ) ≤ (1 / 2 : ℝ) := by
    calc
      (r : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hr1
      _ = (1 / 2 : ℝ) := by norm_num
  have hx0 : 0 ≤ (r : ℝ) * Real.pi := mul_nonneg hr0R Real.pi_pos.le
  have hx2 : (r : ℝ) * Real.pi ≤ 2 := by
    have hmul : (r : ℝ) * Real.pi ≤ (1 / 2 : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hr1R Real.pi_pos.le
    calc (r : ℝ) * Real.pi ≤ (1 / 2 : ℝ) * Real.pi := hmul
      _ = Real.pi / 2 := by ring
      _ ≤ 2 := by nlinarith [Real.pi_lt_four]
  exact sinTaylor_error hx0 hx2 n

/-- Cosine Taylor remainder for rational multiples of `π` in `[0,π/2]`. -/
theorem cos_rational_pi_taylor_error {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    {n : ℕ} (hn : 2 ≤ n) :
    |Real.cos ((r : ℝ) * Real.pi) - cosTaylor ((r : ℝ) * Real.pi) n| ≤
      cosTailTerm ((r : ℝ) * Real.pi) (n - 1) := by
  have hr0R : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1R : (r : ℝ) ≤ (1 / 2 : ℝ) := by
    calc
      (r : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hr1
      _ = (1 / 2 : ℝ) := by norm_num
  have hx0 : 0 ≤ (r : ℝ) * Real.pi := mul_nonneg hr0R Real.pi_pos.le
  have hx2 : (r : ℝ) * Real.pi ≤ 2 := by
    have hmul : (r : ℝ) * Real.pi ≤ (1 / 2 : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hr1R Real.pi_pos.le
    calc (r : ℝ) * Real.pi ≤ (1 / 2 : ℝ) * Real.pi := hmul
      _ = Real.pi / 2 := by ring
      _ ≤ 2 := by nlinarith [Real.pi_lt_four]
  exact cosTaylor_error hx0 hx2 hn

end ASDExplicitGamma.Numerics
