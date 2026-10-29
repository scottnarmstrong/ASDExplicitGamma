module

public import ASDExplicitGamma.AllOrder.ObservableAdapter
public import ASDExplicitGamma.Inverse.HistoryLpSeries
public import ASDExplicitGamma.Numerics.AllOrder.GeometricMoments
public import ASDExplicitGamma.Numerics.AllOrder.Allocations
public import Homogenization.Book.Ch04.Theorems.WidetildeTheta
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! The Lp history assembly from the exact per-depth profile. -/

@[expose] public section

open MeasureTheory
open Homogenization Homogenization.Book
open Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.AllOrder
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- The depth-`t` trace-defect maximum is a measurable function of the cutoff
sample. -/
theorem cutoffTraceDefectMaxAtDepth_measurable (M : ABKModel 2) (m : ℤ)
    (t : ℕ) : Measurable (fun ω => cutoffTraceDefectMaxAtDepth M m ω t) := by
  classical
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu m
  have hX : Measurable X := by
    simpa [X] using Cutoff.measurable_coefficientCutoff M.nu m
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) := by
    intro ω
    simpa [X] using Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m ω
  let R : TriadicCube 2 := originCube 2 m
  let cells := Homogenization.descendantsAtScale R (R.scale - (t : ℤ))
  have hscale : R.scale - (t : ℤ) ≤ R.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le t)
  have hcells : cells.Nonempty := Homogenization.descendantsAtScale_nonempty R hscale
  have hTrace : ∀ Q ∈ cells, Measurable (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet Q) (X ω).toFun (Annealed.sigmaBar M m : ℝ)) := by
    intro Q _hQ
    have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet
      hX hEll Q
    have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet
      hX hEll Q
    have hTraceUL : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)) := by
      change Measurable (fun ω => ∑ i ∈ Finset.univ,
        (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
      apply Finset.measurable_sum
      intro i hi
      exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
    have hTraceLR : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
      change Measurable (fun ω => ∑ i ∈ Finset.univ,
        (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
      apply Finset.measurable_sum
      intro i hi
      exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
    change Measurable (fun ω =>
      (Annealed.sigmaBar M m : ℝ)⁻¹ *
          Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft +
        (Annealed.sigmaBar M m : ℝ) *
          Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight - 4)
    exact (hTraceUL.const_mul _).add (hTraceLR.const_mul _) |>.sub measurable_const
  have hsup : Measurable (cells.sup' hcells fun Q ω =>
      traceDefect (cubeSet Q) (X ω).toFun (Annealed.sigmaBar M m : ℝ)) :=
    Finset.measurable_sup' hcells hTrace
  have heq : (fun ω => cutoffTraceDefectMaxAtDepth M m ω t) =
      cells.sup' hcells (fun Q ω =>
        traceDefect (cubeSet Q) (X ω).toFun (Annealed.sigmaBar M m : ℝ)) := by
    funext ω
    change Ch02.finsetSupReal cells (fun Q =>
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun
        (Annealed.sigmaBar M m : ℝ)) = _
    rw [Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' cells hcells]
    simp [X]
  rw [heq]
  exact hsup

/-- The displayed AO-PER-DEPTH envelope, kept in real-order form so its
exponent can be lowered to the history order before summing. -/
noncomputable def allOrderDepthProfile (gamma p : ℝ) (t : ℕ) : ℝ :=
  let q := p + 3 * (t : ℝ) + 3
  ((3 * 900000 * gamma * q + 13 * 900000 * gamma +
      4350000 * gamma * q * (t : ℝ)) *
      Real.rpow (3 : ℝ) (5 * gamma * ((t : ℝ) + 1))) +
    (Real.exp (-(Real.log 2 / (64 * gamma))) * q ^ 3 *
      Real.rpow (3 : ℝ) (5 * gamma * ((t : ℝ) + 1)))

private theorem allOrderHistory_rpow_factor (gamma s : ℝ) (t : ℕ) :
    Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
        Real.rpow (3 : ℝ) (5 * gamma * ((t : ℝ) + 1)) =
      Real.rpow (3 : ℝ) (5 * gamma) *
        (Real.rpow (3 : ℝ) (-2 * s + 5 * gamma)) ^ t := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hexp : -2 * s * (t : ℝ) + 5 * gamma * ((t : ℝ) + 1) =
      5 * gamma + (-2 * s + 5 * gamma) * (t : ℝ) := by ring
  calc
    _ = Real.rpow (3 : ℝ)
        (-2 * s * (t : ℝ) + 5 * gamma * ((t : ℝ) + 1)) :=
          (Real.rpow_add h3 _ _).symm
    _ = Real.rpow (3 : ℝ) (5 * gamma + (-2 * s + 5 * gamma) * (t : ℝ)) := by rw [hexp]
    _ = Real.rpow (3 : ℝ) (5 * gamma) *
        Real.rpow (3 : ℝ) ((-2 * s + 5 * gamma) * (t : ℝ)) :=
          Real.rpow_add h3 _ _
    _ = Real.rpow (3 : ℝ) (5 * gamma) *
        (Real.rpow (3 : ℝ) (-2 * s + 5 * gamma)) ^ t := by
          congr 1
          calc
            _ = (Real.rpow (3 : ℝ) (-2 * s + 5 * gamma)) ^ (t : ℝ) :=
              Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
            _ = _ := by rw [Real.rpow_natCast]

private theorem allOrderHistory_rpow_monomial_summable (gamma s : ℝ)
    (hgamma : 0 < gamma) (hgs : 8 * gamma ≤ s) (k : ℕ) :
    Summable (fun t : ℕ =>
      (Real.rpow (3 : ℝ) (-2 * s + 5 * gamma)) ^ t * (t : ℝ) ^ k) := by
  let x := Real.rpow (3 : ℝ) (-2 * s + 5 * gamma)
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : x < 1 := by
    dsimp [x]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hxnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hxpos]
    exact hx1
  have hnormsum : Summable (fun t : ℕ => ‖x ^ t * (t : ℝ) ^ k‖) := by
    simpa only [mul_comm] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one k hxnorm)
  exact Summable.of_norm hnormsum

private theorem allOrderHistory_weight_moment_tsum (a x : ℝ) (k : ℕ) :
    (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ k) =
      a * (∑' t : ℕ, (t : ℝ) ^ k * x ^ t) := by
  calc
    _ = ∑' t : ℕ, a * ((t : ℝ) ^ k * x ^ t) :=
      tsum_congr fun t => by ring
    _ = _ := tsum_mul_left

private theorem allOrderHistory_rare_rate (gamma : ℝ)
    (hgamma : 0 < gamma) (hgammaMax : gamma ≤ 17 / 50000) :
    9 / gamma ^ 3 * Real.exp (-(Real.log 2 / (64 * gamma))) ≤
      Real.exp (-(Real.log 2 / (1350 * gamma))) := by
  have hlog9 : Real.log 9 < 11 / 5 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [transfer_log_gates.2.1]
  let gamma0 : ℝ := 17 / 50000
  let r : ℝ := gamma / gamma0
  have hg0 : 0 < gamma0 := by norm_num [gamma0]
  have hr : 0 < r := div_pos hgamma hg0
  have hr1 : r ≤ 1 := by
    dsimp [r, gamma0]
    exact (div_le_one hg0).2 hgammaMax
  have hlogbase : Real.log (1 / gamma0) < 163 / 20 := by
    have h := transfer_log_gates.2.2.2
    simpa [gamma0] using h
  have hinv : 1 / gamma = (1 / gamma0) * (1 / r) := by
    dsimp [r]
    field_simp [hg0.ne', hgamma.ne']
  have hlogsplit : Real.log (1 / gamma) =
      Real.log (1 / gamma0) + Real.log (1 / r) := by
    rw [hinv, Real.log_mul (by positivity) (by positivity)]
  have hlogratio : Real.log (1 / r) ≤ 1 / r - 1 :=
    Real.log_le_sub_one_of_pos (one_div_pos.mpr hr)
  have hrlog : r * Real.log (1 / r) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hlogratio hr.le
    have hcalc : r * (1 / r - 1) = 1 - r := by field_simp [hr.ne']
    rw [hcalc] at hmul
    linarith
  have hlogbound : gamma * (Real.log 9 + 3 * Real.log (1 / gamma)) <
      gamma0 * (593 / 20) := by
    have hlogbase0 : 0 ≤ Real.log (1 / gamma0) :=
      le_of_lt (Real.log_pos (by norm_num [gamma0] : (1 : ℝ) < 1 / gamma0))
    have hlog9pos : 0 ≤ Real.log 9 := by positivity
    have hconst : Real.log 9 + 3 * Real.log (1 / gamma0) <
        11 / 5 + 3 * (163 / 20) := by nlinarith [hlog9, hlogbase]
    have hfirst := mul_le_mul_of_nonneg_right hconst.le (le_of_lt hgamma)
    have hgammaLog : gamma * Real.log (1 / gamma) =
        gamma * Real.log (1 / gamma0) + gamma0 * (r * Real.log (1 / r)) := by
      rw [hlogsplit]
      dsimp [r]
      field_simp [hg0.ne']
    have hgammaBase : gamma * (Real.log 9 + 3 * Real.log (1 / gamma0)) ≤
        gamma0 * (Real.log 9 + 3 * Real.log (1 / gamma0)) :=
      mul_le_mul_of_nonneg_right hgammaMax (by nlinarith [hlog9pos, hlogbase0])
    have hresult : gamma * (Real.log 9 + 3 * Real.log (1 / gamma)) ≤
        gamma0 * (Real.log 9 + 3 * Real.log (1 / gamma0) + 3) := by
      rw [show gamma * (Real.log 9 + 3 * Real.log (1 / gamma)) =
          gamma * (Real.log 9 + 3 * Real.log (1 / gamma0)) +
            3 * (gamma * Real.log (1 / gamma) -
              gamma * Real.log (1 / gamma0)) by ring]
      rw [hgammaLog]
      have hrrest : gamma0 * (r * Real.log (1 / r)) ≤ gamma0 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hrlog hg0.le
      nlinarith [hgammaBase, hrrest]
    have hfinal : Real.log 9 + 3 * Real.log (1 / gamma0) + 3 < 593 / 20 := by
      nlinarith [hlog9, hlogbase]
    exact lt_of_le_of_lt hresult (mul_lt_mul_of_pos_left hfinal hg0)
  have hdelta : 0 < (1 / 64 - 1 / 1350 : ℝ) := by norm_num
  have hmargin : gamma0 * (593 / 20) <
      (69 / 100 : ℝ) * (1 / 64 - 1 / 1350) := by
    norm_num [gamma0]
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 := log_two_gt_69
  have hlogbudget : gamma * (Real.log 9 + 3 * Real.log (1 / gamma)) ≤
      Real.log 2 * (1 / 64 - 1 / 1350) := by
    exact le_of_lt (calc
      _ < gamma0 * (593 / 20) := hlogbound
      _ < (69 / 100) * (1 / 64 - 1 / 1350) := hmargin
      _ ≤ Real.log 2 * (1 / 64 - 1 / 1350) :=
        mul_le_mul_of_nonneg_right hlog2.le hdelta.le)
  have hlogRatio : Real.log (9 / gamma ^ 3) = Real.log 9 + 3 * Real.log (1 / gamma) := by
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hgamma.ne'), Real.log_pow]
    have hinvlog : Real.log (1 / gamma) = -Real.log gamma := by
      rw [show (1 / gamma : ℝ) = gamma⁻¹ by field_simp]
      exact Real.log_inv gamma
    rw [hinvlog]
    ring
  have hratioBound : Real.log (9 / gamma ^ 3) ≤
      Real.log 2 * (1 / 64 - 1 / 1350) / gamma := by
    rw [hlogRatio]
    exact (le_div_iff₀ hgamma).2 (by nlinarith [hlogbudget])
  have hratioExp : 9 / gamma ^ 3 ≤
      Real.exp (Real.log 2 * (1 / 64 - 1 / 1350) / gamma) :=
    (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 9 / gamma ^ 3)).mp hratioBound
  have hexpId :
      Real.exp (Real.log 2 * (1 / 64 - 1 / 1350) / gamma) *
          Real.exp (-(Real.log 2 / (64 * gamma))) =
        Real.exp (-(Real.log 2 / (1350 * gamma))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc
    _ ≤ Real.exp (Real.log 2 * (1 / 64 - 1 / 1350) / gamma) *
        Real.exp (-(Real.log 2 / (64 * gamma))) :=
      mul_le_mul_of_nonneg_right hratioExp (le_of_lt (Real.exp_pos _))
    _ = _ := hexpId

private theorem allOrderHistory_rare_moment_coefficient_bound (s : ℝ)
    (hspos : 0 < s) (hs1 : s ≤ 1) :
    64 * (3 / 2 : ℝ) + 144 * (2 / s) +
      108 * (16 / (3 * s ^ 2)) + 27 * (64 / (3 * s ^ 3)) ≤ 1536 / s ^ 3 := by
  have hs2le : s ^ 2 ≤ 1 := pow_le_one₀ hspos.le hs1
  have hs3le : s ^ 3 ≤ 1 := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ ≤ 1 * 1 := mul_le_mul hs2le hs1 hspos.le (by norm_num)
      _ = 1 := by ring
  have hs3le_s : s ^ 3 ≤ s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right hs2le hspos.le
      _ = s := by ring
  have hs3le_s2 : s ^ 3 ≤ s ^ 2 := by
    rw [pow_succ]
    calc
      s ^ 2 * s ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hs1 (sq_nonneg s)
      _ = s ^ 2 := by ring
  have hrecip0 : 1 ≤ 1 / s ^ 3 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 3)).2
    simpa using hs3le
  have hrecip1 : 1 / s ≤ 1 / s ^ 3 := by
    apply (div_le_div_iff₀ hspos (by positivity : (0 : ℝ) < s ^ 3)).2
    simpa using hs3le_s
  have hrecip2 : 1 / s ^ 2 ≤ 1 / s ^ 3 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 2)
      (by positivity : (0 : ℝ) < s ^ 3)).2
    simpa using hs3le_s2
  have hraw : 64 * (3 / 2 : ℝ) + 144 * (2 / s) +
      108 * (16 / (3 * s ^ 2)) + 27 * (64 / (3 * s ^ 3)) =
      96 + 288 * (1 / s) + 576 * (1 / s ^ 2) + 576 * (1 / s ^ 3) := by
    field_simp [ne_of_gt hspos]
    ring
  rw [hraw]
  have hrecip02 : (1 : ℝ) ≤ 1 / s ^ 3 := hrecip0
  have hrecip12 : 1 / s ≤ 1 / s ^ 3 := hrecip1
  have hrecip22 : 1 / s ^ 2 ≤ 1 / s ^ 3 := hrecip2
  have htotal : 96 + 288 * (1 / s) + 576 * (1 / s ^ 2) +
      576 * (1 / s ^ 3) ≤ 1536 * (1 / s ^ 3) := by
    linarith [hrecip02, hrecip12, hrecip22]
  calc
    _ ≤ 1536 * (1 / s ^ 3) := htotal
    _ = 1536 / s ^ 3 := by ring

private theorem allOrderHistory_rare_scale_identity (d rare p s : ℝ) :
    d * rare * p ^ 3 * (1536 / s ^ 3) =
      (d * 1536) * (rare * p ^ 3 / s ^ 3) := by ring

private theorem allOrderHistory_rare_division_identity (rare p s : ℝ)
    (hs : s ≠ 0) :
    4608 * (rare * p ^ 3 / s ^ 3) = (4608 / s ^ 3) * rare * p ^ 3 := by
  field_simp [hs]

private theorem allOrderHistory_gamma_cube_identity (gamma : ℝ) :
    4608 * gamma ^ 3 = 9 * (8 * gamma) ^ 3 := by ring

private theorem allOrderHistory_cube_mono (gamma s : ℝ)
    (hbase : 0 ≤ 8 * gamma) (hgs : 8 * gamma ≤ s) :
    (8 * gamma) ^ 3 ≤ s ^ 3 := by
  exact pow_le_pow_left₀ hbase hgs 3

private theorem allOrderHistory_rare_budget_factor (gamma s : ℝ)
    (hgamma : 0 < gamma) (hgammaMax : gamma ≤ 17 / 50000)
    (hgs : 8 * gamma ≤ s) :
    (4608 / s ^ 3) * Real.exp (-(Real.log 2 / (64 * gamma))) ≤
      Real.exp (-(Real.log 2 / (1350 * gamma))) := by
  have hspos : 0 < s := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 8) hgamma) hgs
  have hcube := allOrderHistory_cube_mono gamma s
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hgamma.le) hgs
  have hratio : 4608 / s ^ 3 ≤ 9 / gamma ^ 3 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 3)
      (by positivity : (0 : ℝ) < gamma ^ 3)).2
    calc
      4608 * gamma ^ 3 = 9 * (8 * gamma) ^ 3 :=
        allOrderHistory_gamma_cube_identity gamma
      _ ≤ 9 * s ^ 3 := mul_le_mul_of_nonneg_left hcube (by norm_num)
  have hrate := allOrderHistory_rare_rate gamma hgamma hgammaMax
  calc
    _ ≤ (9 / gamma ^ 3) * Real.exp (-(Real.log 2 / (64 * gamma))) :=
      mul_le_mul_of_nonneg_right hratio (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (-(Real.log 2 / (1350 * gamma))) := hrate

private theorem allOrderHistory_rare_budget_factor_mul (gamma s p : ℝ)
    (hgamma : 0 < gamma) (hgammaMax : gamma ≤ 17 / 50000)
    (hgs : 8 * gamma ≤ s) (hp : 1 ≤ p) :
    (4608 / s ^ 3) * Real.exp (-(Real.log 2 / (64 * gamma))) * p ^ 3 ≤
      Real.exp (-(Real.log 2 / (1350 * gamma))) * p ^ 3 := by
  exact mul_le_mul_of_nonneg_right
    (allOrderHistory_rare_budget_factor gamma s hgamma hgammaMax hgs)
    (pow_nonneg (le_trans (by norm_num) hp) 3)

private theorem allOrderHistory_rare_sum_bound
    (gamma s p d rare a x : ℝ)
    (hgamma : 0 < gamma) (hgammaMax : gamma ≤ 17 / 50000)
    (hgs : 8 * gamma ≤ s) (hs1 : s ≤ 1) (hp : 1 ≤ p)
    (hd0 : 0 ≤ d) (hdle : d ≤ 3) (hrare0 : 0 ≤ rare)
    (hrareVal : rare = Real.exp (-(Real.log 2 / (64 * gamma))))
    (hW0 : (∑' t : ℕ, a * x ^ t) ≤ 3 / 2)
    (hW1 : (∑' t : ℕ, a * x ^ t * (t : ℝ)) ≤ 2 / s)
    (hW2 : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) ≤ 16 / (3 * s ^ 2))
    (hW3 : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3) ≤ 64 / (3 * s ^ 3))
    (hRareEq : (∑' t : ℕ, d * (a * x ^ t) *
        (rare * p ^ 3 * (64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 +
          27 * (t : ℝ) ^ 3))) =
      d * rare * p ^ 3 * (64 * (∑' t : ℕ, a * x ^ t) +
        144 * (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
        108 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) +
        27 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3))) :
    (∑' t : ℕ, d * (a * x ^ t) *
        (rare * p ^ 3 * (64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 +
          27 * (t : ℝ) ^ 3))) ≤
      Real.exp (-(Real.log 2 / (1350 * gamma))) * p ^ 3 := by
  have hspos : 0 < s := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 8) hgamma) hgs
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hcoef := allOrderHistory_rare_moment_coefficient_bound s hspos hs1
  have hm0 := mul_le_mul_of_nonneg_left hW0 (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
  have hm1 := mul_le_mul_of_nonneg_left hW1 (by norm_num : (0 : ℝ) ≤ (144 : ℝ))
  have hm2 := mul_le_mul_of_nonneg_left hW2 (by norm_num : (0 : ℝ) ≤ (108 : ℝ))
  have hm3 := mul_le_mul_of_nonneg_left hW3 (by norm_num : (0 : ℝ) ≤ (27 : ℝ))
  have hmoment :
      64 * (∑' t : ℕ, a * x ^ t) +
        144 * (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
        108 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) +
        27 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3) ≤
      64 * (3 / 2 : ℝ) + 144 * (2 / s) +
        108 * (16 / (3 * s ^ 2)) + 27 * (64 / (3 * s ^ 3)) := by
    linarith [hm0, hm1, hm2, hm3]
  have hscale0 : 0 ≤ d * rare * p ^ 3 :=
    mul_nonneg (mul_nonneg hd0 hrare0) (pow_nonneg hp0 3)
  have htotal := mul_le_mul_of_nonneg_left hmoment hscale0
  have hcoefScale := mul_le_mul_of_nonneg_left hcoef hscale0
  have hsumBound :
      (∑' t : ℕ, d * (a * x ^ t) *
        (rare * p ^ 3 * (64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 +
          27 * (t : ℝ) ^ 3))) ≤ (4608 / s ^ 3) * rare * p ^ 3 := by
    have hraw :
        (∑' t : ℕ, d * (a * x ^ t) *
          (rare * p ^ 3 * (64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 +
            27 * (t : ℝ) ^ 3))) ≤ d * rare * p ^ 3 *
          (64 * (3 / 2 : ℝ) + 144 * (2 / s) +
            108 * (16 / (3 * s ^ 2)) + 27 * (64 / (3 * s ^ 3))) := by
      calc
        _ = d * rare * p ^ 3 * (64 * (∑' t : ℕ, a * x ^ t) +
            144 * (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
            108 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) +
            27 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3)) := hRareEq
        _ ≤ _ := htotal
    have hdconst : d * 1536 ≤ 4608 := by
      calc
        d * 1536 ≤ 3 * 1536 := mul_le_mul_of_nonneg_right hdle (by norm_num)
        _ = 4608 := by norm_num
    calc
      _ ≤ d * rare * p ^ 3 * (64 * (3 / 2 : ℝ) + 144 * (2 / s) +
          108 * (16 / (3 * s ^ 2)) + 27 * (64 / (3 * s ^ 3))) := hraw
      _ ≤ d * rare * p ^ 3 * (1536 / s ^ 3) := hcoefScale
      _ = (d * 1536) * (rare * p ^ 3 / s ^ 3) :=
        allOrderHistory_rare_scale_identity d rare p s
      _ ≤ 4608 * (rare * p ^ 3 / s ^ 3) :=
        mul_le_mul_of_nonneg_right hdconst (by positivity)
      _ = (4608 / s ^ 3) * rare * p ^ 3 :=
        allOrderHistory_rare_division_identity rare p s hspos.ne'
  calc
    _ ≤ (4608 / s ^ 3) * rare * p ^ 3 := hsumBound
    _ = (4608 / s ^ 3) * Real.exp (-(Real.log 2 / (64 * gamma))) * p ^ 3 := by
      rw [hrareVal]
    _ ≤ Real.exp (-(Real.log 2 / (1350 * gamma))) * p ^ 3 := by
      exact allOrderHistory_rare_budget_factor_mul gamma s p hgamma hgammaMax hgs hp

private theorem allOrderDepthProfile_nonneg (gamma p : ℝ) (t : ℕ)
    (hgamma : 0 ≤ gamma) (hp : 1 ≤ p) :
    0 ≤ allOrderDepthProfile gamma p t := by
  dsimp [allOrderDepthProfile]
  positivity

/-- The weighted real-order depth profile is summable and fits the frozen
1350-rate history budget. -/
theorem allOrderHistoryProfile_budget (gamma s p : ℝ)
    (hgamma : 0 < gamma) (hgammaMax : gamma ≤ 17 / 50000)
    (hgs : 8 * gamma ≤ s) (hs1 : s ≤ 1) (hp : 1 ≤ p) :
    Summable (fun t : ℕ =>
      (1 - Real.rpow (3 : ℝ) (-2 * s)) *
        Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile gamma p t) ∧
    (∑' t : ℕ,
      (1 - Real.rpow (3 : ℝ) (-2 * s)) *
        Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile gamma p t) ≤
      2 ^ 29 * gamma * p / s ^ 2 +
        Real.exp (-(Real.log 2 / (1350 * gamma))) * p ^ 3 := by
  let x : ℝ := Real.rpow (3 : ℝ) (-2 * s + 5 * gamma)
  let a : ℝ := 1 - Real.rpow (3 : ℝ) (-2 * s)
  let d : ℝ := Real.rpow (3 : ℝ) (5 * gamma)
  let rare : ℝ := Real.exp (-(Real.log 2 / (64 * gamma)))
  let bulkPoly : ℕ → ℝ := fun t => gamma * p *
    (25 * 900000 + (9 * 900000 + 4 * 4350000) * (t : ℝ) +
      3 * 4350000 * (t : ℝ) ^ 2)
  let rarePoly : ℕ → ℝ := fun t => rare * p ^ 3 *
    (64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 + 27 * (t : ℝ) ^ 3)
  let bulkMajor : ℕ → ℝ := fun t => d * (a * x ^ t) * bulkPoly t
  let rareMajor : ℕ → ℝ := fun t => d * (a * x ^ t) * rarePoly t
  let major : ℕ → ℝ := fun t => bulkMajor t + rareMajor t
  have hspos : 0 < s := by linarith
  have ha : 0 ≤ a := by
    dsimp [a]
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith : -2 * s ≤ 0)
    linarith
  have hdpos : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  have hdle : d ≤ 3 := by
    dsimp [d]
    have hsmall : 5 * gamma ≤ 1 := by nlinarith [hgammaMax]
    calc
      _ ≤ Real.rpow (3 : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hsmall
      _ = 3 := by norm_num
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hxlt : x < 1 := by
    dsimp [x]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hsumPow : ∀ k : ℕ, k ≤ 3 →
      Summable (fun t : ℕ => a * x ^ t * (t : ℝ) ^ k) := by
    intro k hk
    have h := allOrderHistory_rpow_monomial_summable gamma s hgamma hgs k
    simpa [x, mul_assoc] using h.mul_left a
  have hMom := complete_depth_moments gamma s hgamma hgs hs1
  have hW0 : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 0) ≤ 3 / 2 := by
    rw [allOrderHistory_weight_moment_tsum]
    simpa [a, x] using hMom.1
  have hW1 : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 1) ≤ 2 / s := by
    rw [allOrderHistory_weight_moment_tsum]
    simpa [a, x] using hMom.2.1
  have hW2 : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) ≤ 16 / (3 * s ^ 2) := by
    rw [allOrderHistory_weight_moment_tsum]
    simpa [a, x] using hMom.2.2.1
  have hW3 : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3) ≤ 64 / (3 * s ^ 3) := by
    rw [allOrderHistory_weight_moment_tsum]
    simpa [a, x] using hMom.2.2.2
  have hW0' : (∑' t : ℕ, a * x ^ t) ≤ 3 / 2 := by simpa using hW0
  have hW1' : (∑' t : ℕ, a * x ^ t * (t : ℝ)) ≤ 2 / s := by simpa using hW1
  have hW2' : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) ≤ 16 / (3 * s ^ 2) := hW2
  have hW3' : (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3) ≤ 64 / (3 * s ^ 3) := hW3
  have hsum0 := hsumPow 0 (by decide)
  have hsum1 := hsumPow 1 (by decide)
  have hsum2 := hsumPow 2 (by decide)
  have hsum3 := hsumPow 3 (by decide)
  have hsum0' : Summable (fun t : ℕ => a * x ^ t) := by simpa using hsum0
  have hsum1' : Summable (fun t : ℕ => a * x ^ t * (t : ℝ)) := by simpa using hsum1
  have hqbound : ∀ t : ℕ, p + 3 * (t : ℝ) + 3 ≤ p * (4 + 3 * (t : ℝ)) := by
    intro t
    have ht : 0 ≤ (t : ℝ) := by positivity
    nlinarith [hp]
  have hbulkCoeff : ∀ t : ℕ,
      3 * 900000 * gamma * (p + 3 * (t : ℝ) + 3) + 13 * 900000 * gamma +
        4350000 * gamma * (p + 3 * (t : ℝ) + 3) * (t : ℝ) ≤ bulkPoly t := by
    intro t
    have ht : 0 ≤ (t : ℝ) := by positivity
    have hq := hqbound t
    have hfirst := mul_le_mul_of_nonneg_left hq
      (by positivity : 0 ≤ 3 * 900000 * gamma)
    have hthird := mul_le_mul_of_nonneg_left hq
      (by positivity : 0 ≤ 4350000 * gamma * (t : ℝ))
    have hconst := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ 13 * 900000 * gamma)
    dsimp [bulkPoly]
    nlinarith
  have hrareCoeff : ∀ t : ℕ,
      rare * (p + 3 * (t : ℝ) + 3) ^ 3 ≤ rarePoly t := by
    intro t
    have hq := hqbound t
    have hpow : (p + 3 * (t : ℝ) + 3) ^ 3 ≤
        (p * (4 + 3 * (t : ℝ))) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hq 3
    have hpoly : (4 + 3 * (t : ℝ)) ^ 3 =
        64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 + 27 * (t : ℝ) ^ 3 := by ring
    have hpos : 0 ≤ rare := le_of_lt (Real.exp_pos _)
    calc
      _ ≤ rare * (p * (4 + 3 * (t : ℝ))) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow hpos
      _ = rarePoly t := by
        dsimp [rarePoly]
        rw [mul_pow, hpoly]
        ring
  have hpoint : ∀ t : ℕ,
      a * Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile gamma p t ≤ major t := by
    intro t
    have hscale := allOrderHistory_rpow_factor gamma s t
    let q : ℝ := p + 3 * (t : ℝ) + 3
    have hprofile : Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
        allOrderDepthProfile gamma p t =
        (d * x ^ t) *
          ((3 * 900000 * gamma * q +
              13 * 900000 * gamma +
              4350000 * gamma * q * (t : ℝ)) + rare * q ^ 3) := by
      change Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
          (((3 * 900000 * gamma * q + 13 * 900000 * gamma +
              4350000 * gamma * q * (t : ℝ)) *
              Real.rpow (3 : ℝ) (5 * gamma * ((t : ℝ) + 1))) +
            (Real.exp (-(Real.log 2 / (64 * gamma))) * q ^ 3 *
              Real.rpow (3 : ℝ) (5 * gamma * ((t : ℝ) + 1)))) = _
      calc
        _ = (Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
            Real.rpow (3 : ℝ) (5 * gamma * ((t : ℝ) + 1))) *
              ((3 * 900000 * gamma * q +
                13 * 900000 * gamma +
                4350000 * gamma * q * (t : ℝ)) +
                Real.exp (-(Real.log 2 / (64 * gamma))) *
                  q ^ 3) := by ring
        _ = _ := by rw [hscale]
    have hcoeff := add_le_add (hbulkCoeff t) (hrareCoeff t)
    have hfac : 0 ≤ d * x ^ t := by positivity
    calc
      _ = a * ((d * x ^ t) *
          ((3 * 900000 * gamma * (p + 3 * (t : ℝ) + 3) +
              13 * 900000 * gamma +
              4350000 * gamma * (p + 3 * (t : ℝ) + 3) * (t : ℝ)) +
            rare * (p + 3 * (t : ℝ) + 3) ^ 3)) := by rw [← hprofile]; ring
      _ ≤ a * ((d * x ^ t) * (bulkPoly t + rarePoly t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoeff hfac) ha
      _ = major t := by dsimp [major, bulkMajor, rareMajor]; ring
  have hmajorExpand : ∀ t : ℕ, major t =
      (d * (gamma * p * (25 * 900000) + rare * p ^ 3 * 64)) * (a * x ^ t) +
      (d * (gamma * p * (9 * 900000 + 4 * 4350000) + rare * p ^ 3 * 144)) *
        (a * x ^ t * (t : ℝ)) +
      (d * (gamma * p * (3 * 4350000) + rare * p ^ 3 * 108)) *
        (a * x ^ t * (t : ℝ) ^ 2) +
      (d * (rare * p ^ 3 * 27)) * (a * x ^ t * (t : ℝ) ^ 3) := by
    intro t
    dsimp [major, bulkMajor, rareMajor, bulkPoly, rarePoly]
    ring
  have hMajorSummable : Summable major := by
    have hs0 := hsum0'.mul_left
      (d * (gamma * p * (25 * 900000) + rare * p ^ 3 * 64))
    have hs1 := hsum1'.mul_left
      (d * (gamma * p * (9 * 900000 + 4 * 4350000) + rare * p ^ 3 * 144))
    have hs2 := hsum2.mul_left
      (d * (gamma * p * (3 * 4350000) + rare * p ^ 3 * 108))
    have hs3 := hsum3.mul_left (d * (rare * p ^ 3 * 27))
    apply (((hs0.add hs1).add hs2).add hs3).congr
    intro t
    exact (hmajorExpand t).symm
  have hBulkEq : (∑' t : ℕ, bulkMajor t) =
      d * gamma * p * (25 * 900000 * (∑' t : ℕ, a * x ^ t) +
        (9 * 900000 + 4 * 4350000) *
          (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
        3 * 4350000 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2)) := by
    have hterm : ∀ t : ℕ, bulkMajor t =
        (d * gamma * p * (25 * 900000)) * (a * x ^ t) +
        (d * gamma * p * (9 * 900000 + 4 * 4350000)) *
          (a * x ^ t * (t : ℝ)) +
        (d * gamma * p * (3 * 4350000)) *
          (a * x ^ t * (t : ℝ) ^ 2) := by
      intro t
      dsimp [bulkMajor, bulkPoly]
      ring
    have h0 := hsum0'.mul_left (d * gamma * p * (25 * 900000))
    have h1 := hsum1'.mul_left (d * gamma * p * (9 * 900000 + 4 * 4350000))
    have h2 := hsum2.mul_left (d * gamma * p * (3 * 4350000))
    calc
      _ = ∑' t : ℕ,
          ((d * gamma * p * (25 * 900000)) * (a * x ^ t) +
            (d * gamma * p * (9 * 900000 + 4 * 4350000)) *
              (a * x ^ t * (t : ℝ)) +
            (d * gamma * p * (3 * 4350000)) *
              (a * x ^ t * (t : ℝ) ^ 2)) := by
                apply tsum_congr
                intro t
                rw [hterm t]
      _ = (∑' t : ℕ, (d * gamma * p * (25 * 900000)) * (a * x ^ t)) +
            (∑' t : ℕ, (d * gamma * p * (9 * 900000 + 4 * 4350000)) *
              (a * x ^ t * (t : ℝ))) +
          (∑' t : ℕ, (d * gamma * p * (3 * 4350000)) *
            (a * x ^ t * (t : ℝ) ^ 2)) := by
              rw [(h0.add h1).tsum_add h2, h0.tsum_add h1]
      _ = _ := by
        have ht0 : (∑' t : ℕ, (d * gamma * p * (25 * 900000)) * (a * x ^ t)) =
            (d * gamma * p * (25 * 900000)) * (∑' t : ℕ, a * x ^ t) := tsum_mul_left
        have ht1 : (∑' t : ℕ, (d * gamma * p * (9 * 900000 + 4 * 4350000)) *
            (a * x ^ t * (t : ℝ))) =
            (d * gamma * p * (9 * 900000 + 4 * 4350000)) *
              (∑' t : ℕ, a * x ^ t * (t : ℝ)) := tsum_mul_left
        have ht2 : (∑' t : ℕ, (d * gamma * p * (3 * 4350000)) *
            (a * x ^ t * (t : ℝ) ^ 2)) =
            (d * gamma * p * (3 * 4350000)) *
              (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) := tsum_mul_left
        rw [ht0, ht1, ht2]
        ring
  have hRareEq : (∑' t : ℕ, rareMajor t) =
      d * rare * p ^ 3 * (64 * (∑' t : ℕ, a * x ^ t) +
        144 * (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
        108 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) +
        27 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3)) := by
    have hterm : ∀ t : ℕ, rareMajor t =
        (d * rare * p ^ 3 * 64) * (a * x ^ t) +
        (d * rare * p ^ 3 * 144) * (a * x ^ t * (t : ℝ)) +
        (d * rare * p ^ 3 * 108) * (a * x ^ t * (t : ℝ) ^ 2) +
        (d * rare * p ^ 3 * 27) * (a * x ^ t * (t : ℝ) ^ 3) := by
      intro t
      dsimp [rareMajor, rarePoly]
      ring
    have h0 := hsum0'.mul_left (d * rare * p ^ 3 * 64)
    have h1 := hsum1'.mul_left (d * rare * p ^ 3 * 144)
    have h2 := hsum2.mul_left (d * rare * p ^ 3 * 108)
    have h3s := hsum3.mul_left (d * rare * p ^ 3 * 27)
    calc
      _ = ∑' t : ℕ,
          ((d * rare * p ^ 3 * 64) * (a * x ^ t) +
            (d * rare * p ^ 3 * 144) * (a * x ^ t * (t : ℝ)) +
            (d * rare * p ^ 3 * 108) * (a * x ^ t * (t : ℝ) ^ 2) +
            (d * rare * p ^ 3 * 27) * (a * x ^ t * (t : ℝ) ^ 3)) := by
              apply tsum_congr
              intro t
              rw [hterm t]
      _ = (∑' t : ℕ, (d * rare * p ^ 3 * 64) * (a * x ^ t)) +
            (∑' t : ℕ, (d * rare * p ^ 3 * 144) *
              (a * x ^ t * (t : ℝ))) +
            (∑' t : ℕ, (d * rare * p ^ 3 * 108) *
              (a * x ^ t * (t : ℝ) ^ 2)) +
            (∑' t : ℕ, (d * rare * p ^ 3 * 27) *
              (a * x ^ t * (t : ℝ) ^ 3)) := by
                rw [((h0.add h1).add h2).tsum_add h3s,
                  (h0.add h1).tsum_add h2, h0.tsum_add h1]
      _ = _ := by
        have ht0 : (∑' t : ℕ, (d * rare * p ^ 3 * 64) * (a * x ^ t)) =
            (d * rare * p ^ 3 * 64) * (∑' t : ℕ, a * x ^ t) := tsum_mul_left
        have ht1 : (∑' t : ℕ, (d * rare * p ^ 3 * 144) *
            (a * x ^ t * (t : ℝ))) =
            (d * rare * p ^ 3 * 144) *
              (∑' t : ℕ, a * x ^ t * (t : ℝ)) := tsum_mul_left
        have ht2 : (∑' t : ℕ, (d * rare * p ^ 3 * 108) *
            (a * x ^ t * (t : ℝ) ^ 2)) =
            (d * rare * p ^ 3 * 108) *
              (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) := tsum_mul_left
        have ht3 : (∑' t : ℕ, (d * rare * p ^ 3 * 27) *
            (a * x ^ t * (t : ℝ) ^ 3)) =
            (d * rare * p ^ 3 * 27) *
              (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3) := tsum_mul_left
        rw [ht0, ht1, ht2, ht3]
        ring
  have hbulkConst : (111 / 2 : ℝ) * 900000 + 24 * 4350000 = 154350000 := by norm_num
  have hbulkAlloc : d * ((111 / 2 : ℝ) * 900000 + 24 * 4350000) ≤ 2 ^ 29 := by
    have halloc := bulk_history_allocations
    have hgate : (463050000 : ℝ) < (2 : ℝ) ^ 29 := by exact_mod_cast halloc.2.1
    have heq : (3 : ℝ) * 154350000 = 463050000 := by norm_num
    rw [hbulkConst]
    nlinarith [hdle, hgate, heq]
  have hbulkBound : (∑' t : ℕ, bulkMajor t) ≤ 2 ^ 29 * gamma * p / s ^ 2 := by
    rw [hBulkEq]
    have hrecip : 1 / s ≤ 1 / s ^ 2 := by
      apply (div_le_div_iff₀ hspos (by positivity : (0 : ℝ) < s ^ 2)).2
      nlinarith [hs1]
    have hrecip' : 1 ≤ 1 / s ^ 2 := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < s ^ 2)).2
      nlinarith [hs1]
    have hcoef : 25 * 900000 * (3 / 2 : ℝ) +
        (9 * 900000 + 4 * 4350000) * (2 / s) +
        3 * 4350000 * (16 / (3 * s ^ 2)) ≤
        ((111 / 2 : ℝ) * 900000 + 24 * 4350000) / s ^ 2 := by
      have hraw : 25 * 900000 * (3 / 2 : ℝ) +
          (9 * 900000 + 4 * 4350000) * (2 / s) +
          3 * 4350000 * (16 / (3 * s ^ 2)) =
          33750000 + 51000000 * (1 / s) + 69600000 * (1 / s ^ 2) := by
        field_simp
        ring
      have hconst0 : (33750000 : ℝ) ≤ 33750000 * (1 / s ^ 2) := by
        calc
          _ = 33750000 * 1 := by ring
          _ ≤ 33750000 * (1 / s ^ 2) :=
            mul_le_mul_of_nonneg_left hrecip' (by norm_num)
      have hconst1 : 51000000 * (1 / s) ≤ 51000000 * (1 / s ^ 2) :=
        mul_le_mul_of_nonneg_left hrecip (by norm_num)
      rw [hraw, hbulkConst]
      calc
        _ ≤ 33750000 * (1 / s ^ 2) + 51000000 * (1 / s ^ 2) +
            69600000 * (1 / s ^ 2) := by linarith
        _ = 154350000 / s ^ 2 := by field_simp; ring
    have hm0 := mul_le_mul_of_nonneg_left hW0'
      (by norm_num : (0 : ℝ) ≤ (25 : ℝ) * 900000)
    have hm1 := mul_le_mul_of_nonneg_left hW1'
      (by norm_num : (0 : ℝ) ≤ (9 : ℝ) * 900000 + 4 * 4350000)
    have hm2 := mul_le_mul_of_nonneg_left hW2'
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) * 4350000)
    have hmoment :
        25 * 900000 * (∑' t : ℕ, a * x ^ t) +
          (9 * 900000 + 4 * 4350000) *
            (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
          3 * 4350000 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) ≤
        25 * 900000 * (3 / 2 : ℝ) +
          (9 * 900000 + 4 * 4350000) * (2 / s) +
          3 * 4350000 * (16 / (3 * s ^ 2)) := by nlinarith [hm0, hm1, hm2]
    have hscaled := mul_le_mul_of_nonneg_left hcoef (by positivity : 0 ≤ d * gamma * p)
    have htotScaled := mul_le_mul_of_nonneg_left hmoment
      (by positivity : 0 ≤ d * gamma * p)
    calc
      _ ≤ d * gamma * p *
          (25 * 900000 * (3 / 2 : ℝ) +
            (9 * 900000 + 4 * 4350000) * (2 / s) +
            3 * 4350000 * (16 / (3 * s ^ 2))) := by nlinarith [htotScaled]
      _ ≤ d * gamma * p *
          (((111 / 2 : ℝ) * 900000 + 24 * 4350000) / s ^ 2) := hscaled
      _ = (d * ((111 / 2 : ℝ) * 900000 + 24 * 4350000)) *
          (gamma * p / s ^ 2) := by ring
      _ ≤ (2 ^ 29) * (gamma * p / s ^ 2) :=
          mul_le_mul_of_nonneg_right hbulkAlloc (by positivity)
      _ = 2 ^ 29 * gamma * p / s ^ 2 := by ring
  have hrareBound : (∑' t : ℕ, rareMajor t) ≤
      Real.exp (-(Real.log 2 / (1350 * gamma))) * p ^ 3 := by
    have hRareEq' : (∑' t : ℕ, d * (a * x ^ t) *
        (rare * p ^ 3 * (64 + 144 * (t : ℝ) + 108 * (t : ℝ) ^ 2 +
          27 * (t : ℝ) ^ 3))) =
        d * rare * p ^ 3 * (64 * (∑' t : ℕ, a * x ^ t) +
          144 * (∑' t : ℕ, a * x ^ t * (t : ℝ)) +
          108 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 2) +
          27 * (∑' t : ℕ, a * x ^ t * (t : ℝ) ^ 3)) := by
      simpa [rareMajor, rarePoly] using hRareEq
    have hrareNonneg : 0 ≤ rare := Real.exp_nonneg _
    simpa [rareMajor, rarePoly] using
      allOrderHistory_rare_sum_bound gamma s p d rare a x hgamma hgammaMax hgs hs1 hp
        hdpos.le hdle hrareNonneg rfl hW0' hW1' hW2' hW3' hRareEq'
  have hbulkNonneg : ∀ t : ℕ, 0 ≤ bulkMajor t := by
    intro t
    dsimp [bulkMajor, bulkPoly]
    positivity
  have hrareNonneg : ∀ t : ℕ, 0 ≤ rareMajor t := by
    intro t
    dsimp [rareMajor, rarePoly]
    positivity
  have hmajorNonneg : ∀ t : ℕ, 0 ≤ major t := by
    intro t
    dsimp [major]
    exact add_nonneg (hbulkNonneg t) (hrareNonneg t)
  have hBulkSummable : Summable bulkMajor := by
    apply hMajorSummable.of_norm_bounded
    intro t
    rw [Real.norm_of_nonneg (hbulkNonneg t)]
    dsimp [major]
    exact le_add_of_nonneg_right (hrareNonneg t)
  have hRareSummable : Summable rareMajor := by
    apply hMajorSummable.of_norm_bounded
    intro t
    rw [Real.norm_of_nonneg (hrareNonneg t)]
    dsimp [major]
    exact le_add_of_nonneg_left (hbulkNonneg t)
  have hmajorTsum : (∑' t : ℕ, major t) =
      (∑' t : ℕ, bulkMajor t) + (∑' t : ℕ, rareMajor t) := by
    calc
      _ = ∑' t : ℕ, (bulkMajor t + rareMajor t) :=
        tsum_congr fun t => by rfl
      _ = _ := hBulkSummable.tsum_add hRareSummable
  have hprofileTermNonneg : ∀ t : ℕ,
      0 ≤ a * Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile gamma p t := by
    intro t
    exact mul_nonneg (mul_nonneg ha (Real.rpow_nonneg (by norm_num) _))
      (allOrderDepthProfile_nonneg gamma p t (by exact le_of_lt hgamma) hp)
  have hprofileSummable : Summable (fun t : ℕ =>
      a * Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile gamma p t) := by
    apply hMajorSummable.of_norm_bounded
    intro t
    rw [Real.norm_of_nonneg (hprofileTermNonneg t)]
    exact hpoint t
  have htotal :
      (∑' t : ℕ, a * Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) *
        allOrderDepthProfile gamma p t) ≤
        2 ^ 29 * gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1350 * gamma))) * p ^ 3 := by
    calc
      _ ≤ ∑' t : ℕ, major t := hprofileSummable.tsum_le_tsum hpoint hMajorSummable
      _ = _ := hmajorTsum
      _ ≤ _ := add_le_add hbulkBound hrareBound
  constructor
  · simpa only [a] using hprofileSummable
  · simpa only [a] using htotal

/-- AO-HISTORY-SUM assembled from its exact per-depth real-order input. The
scalar history allocation is proved internally from the certified geometric
moments and the rare-rate gate. -/
theorem allOrderHistorySum_of_depthProfile (M : ABKModel 2) (m : ℤ) (s : ℝ)
    (hgamma : 0 < M.gamma) (hgammaMax : M.gamma ≤ 17 / 50000)
    (hs : 8 * M.gamma ≤ s) (hs1 : s ≤ 1)
    (hDepth : (M.gamma ≤ 17 / 50000) → ∀ p : ℝ, 1 ≤ p → ∀ t : ℕ,
      eLpNorm (cutoffTraceDefectMaxAtDepth M m · t)
          (ENNReal.ofReal (p + 3 * (t : ℝ) + 3))
          (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (allOrderDepthProfile M.gamma p t)) :
    ∀ ⦃p : ℝ⦄, 1 ≤ p →
      eLpNorm
        (fun ω => Observable.cutoffHomogenizationError M m
        ⟨s, by linarith⟩ ω ^ 2)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (2 ^ 29 * M.gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3) := by
  intro p hp
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let a := 1 - Real.rpow (3 : ℝ) (-2 * s)
  let w : ℕ → ℝ := fun t => Real.rpow (3 : ℝ) (-2 * s * (t : ℝ))
  have hScalarBudget := allOrderHistoryProfile_budget M.gamma s p hgamma hgammaMax hs hs1 hp
  have hBudget : Summable (fun t : ℕ => a * w t * allOrderDepthProfile M.gamma p t) := by
    simpa only [a, w, mul_assoc] using hScalarBudget.1
  have hBudgetBound : (∑' t : ℕ, a * w t * allOrderDepthProfile M.gamma p t) ≤
      2 ^ 29 * M.gamma * p / s ^ 2 +
        Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3 := by
    simpa only [a, w, mul_assoc] using hScalarBudget.2
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ := fun t ω => a * (w t *
    cutoffTraceDefectMaxAtDepth M m ω t)
  have hspos : 0 < s := by linarith
  have ha : 0 ≤ a := by
    dsimp [a]
    have hpw := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith : -2 * s ≤ 0)
    linarith
  have hw : ∀ t, 0 ≤ w t := by
    intro t
    exact Real.rpow_nonneg (by norm_num) _
  have hcoef : ∀ t, 0 ≤ a * w t := fun t => mul_nonneg ha (hw t)
  have hprofile : ∀ t, 0 ≤ allOrderDepthProfile M.gamma p t := by
    intro t
    have hq : 0 ≤ p + 3 * (t : ℝ) + 3 := by positivity
    dsimp [allOrderDepthProfile]
    positivity
  have hFmeas : ∀ t, Measurable (F t) := by
    intro t
    dsimp [F]
    exact ((cutoffTraceDefectMaxAtDepth_measurable M m t).const_mul (w t)).const_mul a
  have hDepthP : ∀ t,
      eLpNorm (cutoffTraceDefectMaxAtDepth M m · t) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (allOrderDepthProfile M.gamma p t) := by
    intro t
    have ht : (0 : ℝ) ≤ (t : ℝ) := by positivity
    have hq : p ≤ p + 3 * (t : ℝ) + 3 := by nlinarith
    have hmono :
        eLpNorm (cutoffTraceDefectMaxAtDepth M m · t) (ENNReal.ofReal p) μ ≤
          eLpNorm (cutoffTraceDefectMaxAtDepth M m · t)
            (ENNReal.ofReal (p + 3 * (t : ℝ) + 3)) μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (f := fun ω =>
        cutoffTraceDefectMaxAtDepth M m ω t) (μ := μ) (ENNReal.ofReal_le_ofReal hq)
    exact (hmono.trans (hDepth hgammaMax p hp t))
  have hTerm : ∀ t,
      eLpNorm (F t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        ((1 - Real.rpow (3 : ℝ) (-2 * s)) *
          Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile M.gamma p t) := by
    intro t
    have hconst : eLpNorm (F t) (ENNReal.ofReal p) μ =
        ENNReal.ofReal (a * w t) *
          eLpNorm (cutoffTraceDefectMaxAtDepth M m · t) (ENNReal.ofReal p) μ := by
      dsimp [F]
      rw [show (fun ω => a * (w t * cutoffTraceDefectMaxAtDepth M m ω t)) =
        (a * w t) • (fun ω => cutoffTraceDefectMaxAtDepth M m ω t) by
          funext ω
          simp [smul_eq_mul]
          ring]
      rw [eLpNorm_const_smul]
      simp [Real.enorm_eq_ofReal (hcoef t)]
    rw [hconst]
    calc
      _ ≤ ENNReal.ofReal (a * w t) * ENNReal.ofReal (allOrderDepthProfile M.gamma p t) :=
        mul_le_mul_of_nonneg_left (hDepthP t) (bot_le : (0 : ℝ≥0∞) ≤ _)
      _ = ENNReal.ofReal
          ((1 - Real.rpow (3 : ℝ) (-2 * s)) *
            Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile M.gamma p t) := by
        rw [← ENNReal.ofReal_mul (hcoef t)]
  have hsumBound : (∑' t : ℕ, eLpNorm (F t) (ENNReal.ofReal p) μ) ≤
      ENNReal.ofReal
        (2 ^ 29 * M.gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3) := by
    calc
      _ ≤ ∑' t : ℕ, ENNReal.ofReal
          ((1 - Real.rpow (3 : ℝ) (-2 * s)) *
            Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile M.gamma p t) :=
          ENNReal.tsum_le_tsum (hTerm)
      _ = ENNReal.ofReal
          (∑' t : ℕ,
            (1 - Real.rpow (3 : ℝ) (-2 * s)) *
              Real.rpow (3 : ℝ) (-2 * s * (t : ℝ)) * allOrderDepthProfile M.gamma p t) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun t => mul_nonneg (mul_nonneg ha (hw t)) (hprofile t)) hBudget]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hBudgetBound
  have hfinite : (∑' t : ℕ, eLpNorm (F t) (ENNReal.ofReal p) μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumBound
  have hseries := ASDExplicitGamma.Inverse.eLpNorm_tsum_le_of_finite
    μ (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr hp) F hFmeas hfinite
  have hmajor := cutoffHomogenizationError_sq_le_traceDefect_depth_sum M m s hs hs1
  have hmajor' : (fun ω => Observable.cutoffHomogenizationError M m
      ⟨s, by linarith⟩ ω ^ 2) ≤ᵐ[μ] (fun ω => ∑' t : ℕ, F t ω) := by
    filter_upwards [hmajor] with ω hω
    have hseriesEq : (∑' t : ℕ, F t ω) =
        a * ∑' t : ℕ, w t * cutoffTraceDefectMaxAtDepth M m ω t := by
      dsimp [F]
      rw [← tsum_mul_left]
    rw [hseriesEq]
    exact hω
  have hEmeas : Measurable (fun ω => Observable.cutoffHomogenizationError M m
      ⟨s, by linarith⟩ ω ^ 2) := by
    exact (Observable.measurable_cutoffHomogenizationError M m ⟨s, by linarith⟩).pow_const 2
  have hmajorNorm : ∀ᵐ ω ∂μ,
      ‖Observable.cutoffHomogenizationError M m ⟨s, by linarith⟩ ω ^ 2‖ ≤
        (∑' t : ℕ, F t ω) := by
    filter_upwards [hmajor'] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hω
  have hmono := eLpNorm_mono_ae_real (μ := μ) (p := ENNReal.ofReal p)
    hEmeas.aestronglyMeasurable hmajorNorm
  exact hmono.trans (hseries.trans hsumBound)

end ASDExplicitGamma.AllOrder
