module

public import ASDExplicitGamma.Cold.PlateauCutoffDerivative
public import Homogenization.Sobolev.H1.BasicLemmas

/-! # Weak gradients of globally Lipschitz cutoffs

This uses Mathlib's proved integration-by-parts theorem for line derivatives and
Rademacher's theorem, rather than assuming that a pointwise derivative is a weak gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- The measurable directional derivative representative of a Lipschitz weak gradient. -/
def lipschitzWeakGradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) (i : Fin d) : ℝ :=
  lineDeriv ℝ f x (basisVec i)

/-- Global Lipschitz functions have the displayed weak derivatives on every open domain. -/
theorem hasWeakGradientOn_of_lipschitz {d : ℕ} {f : Vec d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (U : Set (Vec d)) :
    HasWeakGradientOn U f (lipschitzWeakGradient f) := by
  intro i φ hφ hφc hφU
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  have hglobal := hf.integral_lineDeriv_mul_eq (μ := volume) hD hφc (basisVec i)
  have hdiff : ∀ x, DifferentiableAt ℝ φ x := fun x =>
    (hφ.differentiable (by simp)) x
  simp_rw [(hdiff _).lineDeriv_eq_fderiv, map_neg, neg_mul, integral_neg] at hglobal
  have htest : ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) =
      ∫ x, f x * (fderiv ℝ φ x) (basisVec i) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport φ := fun h => hx (hφU h)
    have he : φ =ᶠ[𝓝 x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hnot |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [he.fderiv_eq]
    simp
  have hgrad : ∫ x in U, lipschitzWeakGradient f x i * φ x =
      ∫ x, lipschitzWeakGradient f x i * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hnot : x ∉ tsupport φ := fun h => hx (hφU h)
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  rw [htest, hgrad]
  have heq : ∫ x, (fderiv ℝ φ x) (basisVec i) * f x =
      ∫ x, f x * (fderiv ℝ φ x) (basisVec i) := by
    congr 1; funext x; ring
  rw [heq] at hglobal
  change (∫ x, f x * (fderiv ℝ φ x) (basisVec i)) =
    -(∫ x, lineDeriv ℝ f x (basisVec i) * φ x)
  linarith only [hglobal]

/-- The chosen weak derivative agrees almost everywhere with the classical derivative. -/
theorem lipschitzWeakGradient_ae_eq_fderiv {d : ℕ} {f : Vec d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    ∀ᵐ x ∂volume, ∀ i, lipschitzWeakGradient f x i = (fderiv ℝ f x) (basisVec i) := by
  filter_upwards [hf.ae_differentiableAt] with x hx
  intro i
  exact hx.lineDeriv_eq_fderiv

/-- A finite-measure domain and an L² value bound give an actual H¹ cutoff witness. -/
def lipschitzH1On {d : ℕ} {f : Vec d → ℝ} {C : ℝ≥0} (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U)] (hf : LipschitzWith C f)
    (hvalue : MemL2On U f) : H1Function U where
  toFun := f
  grad := lipschitzWeakGradient f
  memL2 := hvalue
  gradMemL2 := by
    intro i
    exact (hf.memLp_lineDeriv (μ := volume.restrict U) (basisVec i)).mono_exponent (by simp)
  hasWeakGradient := hasWeakGradientOn_of_lipschitz hf U

end ASDExplicitGamma.Cold
