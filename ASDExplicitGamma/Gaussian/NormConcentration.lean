module

public import ASDExplicitGamma.Gaussian.NormingSequence
public import ASDExplicitGamma.Gaussian.ConcentrationCountable
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Sharp Gaussian concentration for norms of finite Hilbert covariance images -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Riesz representers turn a countable norming family into Gaussian linear forms,
with the same Hilbert-to-Banach operator bound. -/
theorem exists_norming_gaussian_linearForms {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] E) {L : ℝ} (hT : ‖T‖ ≤ L) :
    ∃ a : ℕ → Fin n → ℝ, (∀ j, ‖WithLp.toLp 2 (a j)‖ ≤ L) ∧
      ∀ j x, gaussianFiniteLinearForm (a j) x =
        normingSequence E j (T (WithLp.toLp 2 x)) := by
  let f (j : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := (normingSequence E j).comp T
  let z (j : ℕ) : EuclideanSpace ℝ (Fin n) := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (f j)
  let a : ℕ → Fin n → ℝ := fun j i => z j i
  have hcoeff (j : ℕ) : ‖WithLp.toLp 2 (a j)‖ ≤ L := by
    change ‖z j‖ ≤ L
    calc
      ‖z j‖ = ‖f j‖ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _
      _ ≤ ‖normingSequence E j‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * L := mul_le_mul (norm_normingSequence_le E j) hT (norm_nonneg T) (by norm_num)
      _ = L := one_mul L
  have hform (j : ℕ) (x : Fin n → ℝ) :
      gaussianFiniteLinearForm (a j) x = normingSequence E j (T (WithLp.toLp 2 x)) := by
    have hh := congrArg (fun l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => l (WithLp.toLp 2 x))
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).apply_symm_apply (f j))
    change ⟪z j, WithLp.toLp 2 x⟫ = f j (WithLp.toLp 2 x) at hh
    calc
      _ = ⟪z j, WithLp.toLp 2 x⟫ := by
        change (∑ i, z j i * x i) = ⟪WithLp.toLp 2 (a j), WithLp.toLp 2 x⟫
        rw [EuclideanSpace.inner_toLp_toLp]
        simp only [dotProduct, star_trivial, mul_comm, a]
      _ = _ := hh
  exact ⟨a, hcoeff, hform⟩

/-- A finite Gaussian vector mapped into any separable real normed space has the sharp
mean-centered norm tail, with the Hilbert-to-Banach operator norm. -/
theorem measure_centered_tail_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] E)
    {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t) (hT : ‖T‖ ≤ L) :
    Integrable (fun x : Fin n → ℝ => ‖T (WithLp.toLp 2 x)‖) (standardGaussianPi n) ∧
      (standardGaussianPi n).real {x | t ≤ ‖T (WithLp.toLp 2 x)‖ -
        ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n} ≤
        Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  obtain ⟨a, hcoeff, hform⟩ := exists_norming_gaussian_linearForms T hT
  have hsup : gaussianCountableSup a = fun x : Fin n → ℝ => ‖T (WithLp.toLp 2 x)‖ := by
    funext x
    unfold gaussianCountableSup
    simp_rw [hform]
    exact (norm_eq_iSup_normingSequence E (T (WithLp.toLp 2 x))).symm
  have hh := measure_centered_tail_le_of_gaussianCountableSup a hL ht hcoeff
  rwa [hsup] at hh

end ASDExplicitGamma.Gaussian
