module

public import ASDExplicitGamma.Native.GenericSourceMeanTransport
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Mean transport with derivatives only at strictly positive heat times. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Set
noncomputable section

/-- The heat path need only be continuous at zero. The integrating factor
uses derivatives solely inside the interval, as supplied by Gaussian heat. -/
theorem native_source_scalar_mean_of_interior_derivative
    (f df : ℝ → ℝ) (a K L : ℝ) (hK : 0 < K)
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (df t) t)
    (hstart : f 0 ≤ a)
    (hdrift : ∀ t ∈ Ioo (0:ℝ) 1, df t ≤ K*f t+L) :
    f 1 ≤ a*Real.exp K+L*nativeSourcePhiOne K := by
  let g := fun t => (f t+L/K)*Real.exp (-K*t)
  let dg := fun t => (df t-K*(f t+L/K))*Real.exp (-K*t)
  have hg : ContinuousOn g (Icc (0:ℝ) 1) :=
    (hf.add continuousOn_const).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hdg (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt g (dg t) t := by
    have hh := ((hdf t ht).add_const (L/K)).mul (((hasDerivAt_id t).const_mul (-K)).exp)
    have hgfun : g = (fun x => f x+L/K)*(fun x => Real.exp (-K*id x)) := rfl
    rw [hgfun]
    convert hh using 1
    dsimp [dg]
    ring
  have hdg0 (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : dg t ≤ 0 := by
    have hh := hdrift t ht
    have hdiv : K*(L/K)=L := by field_simp
    change (df t-K*(f t+L/K))*Real.exp (-K*t) ≤ 0
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    linarith only [hh,hdiv]
  have hanti : AntitoneOn g (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hg
    · intro t ht
      rw [interior_Icc] at ht
      exact (hdg t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hdg0 t ht
  have hh := hanti (by constructor <;> norm_num : (0:ℝ)∈Icc 0 1)
    (by constructor <;> norm_num : (1:ℝ)∈Icc 0 1) (by norm_num : (0:ℝ)≤1)
  have hprod := mul_le_mul_of_nonneg_right hh (Real.exp_pos K).le
  have hexp : Real.exp (-K)*Real.exp K=1 := by rw [←Real.exp_add]; simp
  have hbound : f 1 ≤ (a+L/K)*Real.exp K-L/K := by
    dsimp [g] at hprod
    simp only [mul_one,mul_zero,Real.exp_zero] at hprod
    rw [mul_assoc,hexp,mul_one] at hprod
    have hinit := mul_le_mul_of_nonneg_right (add_le_add_right hstart (L/K)) (Real.exp_pos K).le
    linarith only [hprod,hinit]
  have hphi := native_source_phiOne_mul K
  have hid : (a+L/K)*Real.exp K-L/K=a*Real.exp K+L*nativeSourcePhiOne K := by
    field_simp [hK.ne']
    nlinarith only [congrArg (fun r : ℝ => L*r) hphi]
  exact hbound.trans_eq hid

end
end ASDExplicitGamma.Native
