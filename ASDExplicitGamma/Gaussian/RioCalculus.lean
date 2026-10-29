module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Scalar calculus behind the sharp L20 one-step estimate -/

@[expose] public section
noncomputable section
open Set
namespace ASDExplicitGamma.Gaussian

/-- A zero first derivative and nonnegative second derivative give a global minimum. -/
theorem rio_minimum_of_second_nonneg {f g h : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hn : ∀ x, 0 ≤ h x) (h0 : g 0 = 0) (x : ℝ) : f 0 ≤ f x := by
  have hc : ConvexOn ℝ univ f := convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).continuousOn
    (fun x _ => (hf x).hasDerivWithinAt) (fun x _ => (hg x).hasDerivWithinAt) (fun x _ => hn x)
  rcases lt_trichotomy 0 x with hx | hx | hx
  · have hs := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ x) hx (hf 0)
    rw [h0,slope_def_field,sub_zero] at hs
    have h := (le_div_iff₀ hx).mp hs
    linarith only [h]
  · subst x
    exact le_rfl
  · have hs := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ 0) hx (hf 0)
    rw [h0,slope_def_field] at hs
    have h := (div_le_iff₀ (by linarith : 0 < 0-x)).mp hs
    linarith only [h]

/-- The source Taylor bound follows from an upper bound on the actual second derivative. -/
theorem rio_quadratic_bound {f g h : ℝ → ℝ} {K : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hle : ∀ x, h x ≤ K) (h0 : g 0 = 0) : f 1 ≤ f 0+K/2 := by
  let F := fun x => K/2*x^2-f x
  let G := fun x => K*x-g x
  have hF (x : ℝ) : HasDerivAt F (G x) x := by
    have h := (((hasDerivAt_id x).pow 2).const_mul (K/2)).sub (hf x)
    convert h using 1
    · rfl
    · dsimp only [G,id_eq]
      norm_num
      ring
  have hG (x : ℝ) : HasDerivAt G (K-h x) x := by
    convert ((hasDerivAt_id x).const_mul K).sub (hg x) using 1
    · rfl
    · ring
  have hF0 : G 0 = 0 := by dsimp [G]; rw [h0]; ring
  have h := rio_minimum_of_second_nonneg hF hG (fun x => sub_nonneg.mpr (hle x)) hF0 1
  dsimp [F] at h
  norm_num at h
  linarith only [h]

end ASDExplicitGamma.Gaussian
