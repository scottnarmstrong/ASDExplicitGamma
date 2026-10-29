module

public import ASDExplicitGamma.Gaussian.GeneratorAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Exact covariance centering along a constant-skew gauge direction. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
noncomputable section

theorem pureFlux_fderiv_gauge_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hf : Differentiable ℝ f) (z : E)
    (hinv : ∀ x : E, ∀ t : ℝ, f (x+t • z) = f x) (x : E) :
    fderiv ℝ f x z = 0 := by
  have hd := (hf x).hasFDerivAt.hasLineDerivAt z
  change HasDerivAt (fun t : ℝ => f (x+t • z)) (fderiv ℝ f x z) 0 at hd
  have heq : (fun t : ℝ => f (x+t • z)) = fun _ => f x := funext (hinv x)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 (f x))

theorem pureFlux_secondDirectionalDerivative_sub_gauge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 2 f) (z : E)
    (hinv : ∀ x : E, ∀ t : ℝ, f (x+t • z) = f x) (x H : E) :
    secondDirectionalDerivative f x (H-z) = secondDirectionalDerivative f x H := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable_one
  have heval (v : E) : fderiv ℝ (fun y => fderiv ℝ f y v) x =
      (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x) := by
    exact ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x
      (hdf x).hasFDerivAt).fderiv
  have hzero : (fun y => fderiv ℝ f y z) = fun _ => 0 :=
    funext (pureFlux_fderiv_gauge_eq_zero f (hf.differentiable (by norm_num)) z hinv)
  have hk (v : E) : fderiv ℝ (fderiv ℝ f) x v z = 0 := by
    have hh := congrArg (fun T : E →L[ℝ] ℝ => T v) (heval z)
    rw [hzero] at hh
    simpa only [fderiv_const_apply, zero_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using hh.symm
  have hsym : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hk' (v : E) : fderiv ℝ (fderiv ℝ f) x z v = 0 := by
    rw [hsym.eq z v]
    exact hk v
  unfold secondDirectionalDerivative
  rw [heval, heval]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    map_sub, ContinuousLinearMap.sub_apply, hk, hk', sub_zero, zero_sub]

/-- Covariance contraction is unchanged when each direction loses a gauge mode. -/
theorem pureFlux_modelCovarianceTrace_sub_gauges {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (H z : ℕ → E)
    (hinv : ∀ j : ℕ, ∀ x : E, ∀ t : ℝ, f (x+t • z j) = f x) (x : E) :
    modelCovarianceTrace f (fun j => H j-z j) x = modelCovarianceTrace f H x := by
  unfold modelCovarianceTrace
  exact tsum_congr fun j => pureFlux_secondDirectionalDerivative_sub_gauge f hf (z j) (hinv j) x (H j)

end
end ASDExplicitGamma.Inverse
