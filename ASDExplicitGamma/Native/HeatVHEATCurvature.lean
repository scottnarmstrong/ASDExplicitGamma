module

public import ASDExplicitGamma.Native.HeatQuadraticMoments
public import ASDExplicitGamma.Gaussian.BackwardHeat
public import ASDExplicitGamma.Gaussian.GeneratorSplit
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Gaussian.ModelHeatResponse

/-! # True-frame curvature of the native constant-shear trace -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

theorem nativeHeat_secondDirectionalDerivative_eq_deriv_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x v : E) :
    secondDirectionalDerivative f x v =
      deriv (deriv (fun t : ℝ => f (x + t • v))) 0 := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  let G : E → ℝ := fun y => fderiv ℝ f y v
  let φ : ℝ → ℝ := fun t => f (x + t • v)
  have hfirst (t : ℝ) : deriv φ t = G (x + L t) := by
    have houter := (hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      (x + L t)).hasFDerivAt
    have hinner : HasFDerivAt (fun z : ℝ => x + L z) L t :=
      L.hasFDerivAt.const_add x
    have hcomp := houter.comp t hinner
    have hderiv := hcomp.hasDerivAt.deriv
    simpa [φ, G, L, Function.comp_def] using hderiv
  have hEval := hf.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1 (fun y : E => (y, v)) :=
    contDiff_id.prodMk contDiff_const
  have hG : ContDiff ℝ 1 G := by
    simpa [G, Function.comp_def] using hEval.comp hpair
  have hcomp := (hG.differentiable_one (x + L 0)).hasFDerivAt.comp (0 : ℝ)
    (L.hasFDerivAt.const_add x)
  have hsecondLine : deriv (fun t : ℝ => G (x + L t)) 0 =
      fderiv ℝ G x v := by
    have hderiv := hcomp.hasDerivAt.deriv
    simpa [G, L, Function.comp_def] using hderiv
  have hfirstFun : deriv φ = fun t : ℝ => G (x + L t) :=
    funext hfirst
  calc
    secondDirectionalDerivative f x v = fderiv ℝ G x v := by
      rfl
    _ = deriv (deriv φ) 0 := by
      rw [hfirstFun]
      exact hsecondLine.symm
    _ = deriv (deriv (fun t : ℝ => f (x + t • v))) 0 := rfl

theorem nativeHeat_secondDirectionalDerivative_eq_two_mul_of_quadratic_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x v : E) (a b c : ℝ)
    (hline : ∀ t : ℝ, f (x + t • v) = a + b * t + c * t ^ 2) :
    secondDirectionalDerivative f x v = 2 * c := by
  rw [nativeHeat_secondDirectionalDerivative_eq_deriv_line hf x v]
  let p : ℝ → ℝ := fun t => a + b * t + c * t ^ 2
  have hfun : (fun t : ℝ => f (x + t • v)) = p := by
    funext t
    exact hline t
  rw [hfun]
  have hpoly (t : ℝ) : HasDerivAt p (b + 2 * c * t) t := by
    have hlin : HasDerivAt (fun s : ℝ => b * s) b t := by
      simpa [mul_comm] using (hasDerivAt_id t).const_mul b
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hquad : HasDerivAt (fun s : ℝ => c * s ^ 2) (2 * c * t) t := by
      convert (hasDerivAt_const t c).mul hpow using 1
      all_goals ring_nf
    have hsum := (hasDerivAt_const t a).add (hlin.add hquad)
    have hpFun : p = (fun _ : ℝ => a) +
        ((fun s : ℝ => b * s) + fun s : ℝ => c * s ^ 2) := by
      funext s
      simp [p]
      ring
    rw [← hpFun] at hsum
    simpa [zero_add] using hsum
  have hderivFun : deriv p = fun t : ℝ => b + 2 * c * t :=
    funext fun t => (hpoly t).deriv
  have hsecond : HasDerivAt (fun t : ℝ => b + 2 * c * t) (2 * c) 0 := by
    convert (hasDerivAt_const (0 : ℝ) b).add
      ((hasDerivAt_const (0 : ℝ) (2 * c)).mul (hasDerivAt_id (0 : ℝ))) using 1
    · funext t
      simp
    · ring
  rw [hderivFun]
  exact hsecond.deriv

end ASDExplicitGamma.Native
