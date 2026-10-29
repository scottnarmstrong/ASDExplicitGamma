module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Interior-time integrating-factor comparison for the signed parent
inverse charge. This scalar lemma does not supply a physical generator bound. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Set
noncomputable section

/-- A lower heat drift and the genuine OLD initial value control the
inverse mean using only interior-time derivatives. -/
theorem parent_boundary_inverse_interior_lower
    (f df : ℝ → ℝ) (kappa rho : ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (df t) t)
    (hstart : 2≤f 0)
    (hdrift : ∀ t ∈ Ioo (0:ℝ) 1, -kappa*f t-kappa*rho≤df t)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    (2+rho)*Real.exp (-kappa*t)-rho≤f t := by
  let g := fun s => (f s+rho)*Real.exp (kappa*s)
  have hg : ContinuousOn g (Icc (0:ℝ) 1) :=
    (hf.add continuousOn_const).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hdg (s : ℝ) (hs : s∈Ioo (0:ℝ) 1) :
      HasDerivAt g ((df s+kappa*(f s+rho))*Real.exp (kappa*s)) s := by
    have hh := ((hdf s hs).add_const rho).mul
      (((hasDerivAt_id s).const_mul kappa).exp)
    change HasDerivAt ((fun s => f s+rho)*(fun s => Real.exp (kappa*id s))) _ s
    convert hh using 1
    dsimp
    ring
  have hmono : MonotoneOn g (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hg
    · intro s hs
      rw [interior_Icc] at hs
      exact (hdg s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      apply mul_nonneg _ (Real.exp_pos _).le
      linarith only [hdrift s hs]
  have hh := hmono (by constructor <;> norm_num : (0:ℝ)∈Icc 0 1) ht ht.1
  have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-kappa*t)).le
  have hexp : Real.exp (kappa*t)*Real.exp (-kappa*t)=1 := by
    rw [←Real.exp_add]
    simp
  dsimp [g] at hmul
  simp only [mul_zero,Real.exp_zero,mul_one] at hmul
  rw [mul_assoc,hexp,mul_one] at hmul
  have hi := mul_le_mul_of_nonneg_right (add_le_add_right hstart rho)
    (Real.exp_pos (-kappa*t)).le
  linarith only [hmul,hi]

/-- Keep the actual nonnegative signed inverse energy outside the
integrating-factor comparison. -/
theorem parent_boundary_inverse_interior_charge
    (f df : ℝ → ℝ) (Y kappa rho : ℝ) (hY : 0≤Y)
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (df t) t)
    (hstart : 2≤f 0)
    (hdrift : ∀ t ∈ Ioo (0:ℝ) 1, -kappa*f t-kappa*rho≤df t)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    -Y*(f t-2)≤Y*(2+rho)*(1-Real.exp (-kappa*t)) := by
  have hh := mul_le_mul_of_nonneg_left
    (parent_boundary_inverse_interior_lower f df kappa rho hf hdf hstart hdrift t ht) hY
  nlinarith only [hh]

end
end ASDExplicitGamma.Native
