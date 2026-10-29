module

public import ASDExplicitGamma.Inverse.StoppedTailKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact polynomial-exponential primitives for the source rare diameter moments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- The source integrated rare-moment polynomial. Its recursion is the
repeated integration-by-parts formula with exponential length four. -/
def rareMomentPolynomial : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, t => t^(n+1)+4*(n+1)*rareMomentPolynomial n t

/-- A primitive of t^n exp(-t/4), retaining the exact endpoint terms. -/
def rareMomentPrimitive : ℕ → ℝ → ℝ
  | 0, t => -4*Real.exp (-t/4)
  | n+1, t => -4*t^(n+1)*Real.exp (-t/4)+4*(n+1)*rareMomentPrimitive n t

theorem rare_moment_primitive_eq (n : ℕ) (t : ℝ) :
    rareMomentPrimitive n t = -4*rareMomentPolynomial n t*Real.exp (-t/4) := by
  induction n with
  | zero => simp only [rareMomentPrimitive,rareMomentPolynomial,mul_one]
  | succ n ih =>
    simp only [rareMomentPrimitive,rareMomentPolynomial,ih]
    ring

theorem rare_moment_primitive_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (rareMomentPrimitive n) (x^n*Real.exp (-x/4)) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t/4)) (-(1/4:ℝ)*Real.exp (-x/4)) x := by
    simpa only [Pi.neg_apply,id_eq,mul_comm,neg_div] using! ((hasDerivAt_id x).neg.div_const 4).exp
  induction n with
  | zero =>
    change HasDerivAt (fun t : ℝ => -4*Real.exp (-t/4)) (x^0*Real.exp (-x/4)) x
    convert he.const_mul (-4) using 1
    ring
  | succ n ih =>
    change HasDerivAt (fun t : ℝ => -4*t^(n+1)*Real.exp (-t/4)+4*(n+1)*rareMomentPrimitive n t)
      (x^(n+1)*Real.exp (-x/4)) x
    have hp := (((hasDerivAt_id x).pow (n+1)).mul he).const_mul (-4)
    simp only [Pi.pow_apply,Pi.mul_apply,id_eq] at hp
    have hq := ih.const_mul (4*(n+1:ℝ))
    convert hp.add hq using 1
    · funext t
      dsimp only [Pi.add_apply]
      ring
    · norm_num only [Nat.add_sub_cancel]
      push_cast
      ring

theorem rare_moment_primitive_tendsto (n : ℕ) :
    Tendsto (rareMomentPrimitive n) atTop (𝓝 0) := by
  have hp (k : ℕ) : Tendsto (fun x : ℝ => x^k*Real.exp (-x/4)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) (1/4) (by norm_num) using 1
    funext x
    rw [Real.rpow_natCast]
    congr 2
    ring
  induction n with
  | zero =>
    convert (hp 0).const_mul (-4) using 1
    · funext t
      simp only [rareMomentPrimitive,pow_zero,one_mul]
    · norm_num
  | succ n ih =>
    convert ((hp (n+1)).const_mul (-4)).add (ih.const_mul (4*(n+1:ℝ))) using 1
    · funext t
      simp only [rareMomentPrimitive]
      ring
    · norm_num

/-- The complete improper moment tail, with no dropped endpoint contribution. -/
theorem rare_moment_tail_integral (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : ℝ in Ioi t, x^n*Real.exp (-x/4)) =
      4*rareMomentPolynomial n t*Real.exp (-t/4) := by
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x (_ : x ∈ Ici t) => rare_moment_primitive_deriv n x)
    (fun x hx => mul_nonneg (pow_nonneg (ht.trans hx.le) n) (Real.exp_pos _).le)
    (rare_moment_primitive_tendsto n)
  rw [rare_moment_primitive_eq] at hh
  simpa only [zero_sub,neg_mul,neg_neg] using! hh

end
end ASDExplicitGamma.Inverse
