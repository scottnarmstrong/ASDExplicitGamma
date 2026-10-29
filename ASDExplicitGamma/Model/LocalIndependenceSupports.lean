module

public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Model.Q3Cov
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import ASDExplicitGamma.Model.Cutoff
public import Mathlib.Probability.Independence.Basic

/-! The actual product-q3 kernel support geometry for arbitrary restriction families. -/
@[expose] public section
namespace ASDExplicitGamma.Model
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions

/-- Interior of the full spatial support of a shell kernel based at x.
The q3 kernel vanishes at the omitted boundary. -/
def shellKernelSupport (k : ℤ) (x : Vec 2) : Set (Vec 2) :=
  {y | ∀ i : Fin 2, |y i - x i| < (3 : ℝ) ^ k / 2}

/-- Disjoint full kernel supports force a separating coordinate at one shell length. -/
theorem shellKernelSupport_separation (k : ℤ) (x y : Vec 2)
    (hxy : Disjoint (shellKernelSupport k x) (shellKernelSupport k y)) :
    ∃ i : Fin 2, (3 : ℝ) ^ k ≤ |(x - y) i| := by
  by_contra hn
  have hclose : ∀ i : Fin 2, |x i - y i| < (3 : ℝ) ^ k := by
    intro i
    exact lt_of_not_ge (fun hi => hn ⟨i, hi⟩)
  have hx : (fun i => (x i + y i) / 2) ∈ shellKernelSupport k x := by
    intro i
    have he : (x i + y i) / 2 - x i = -(x i - y i) / 2 := by ring
    rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_lt_div_of_pos_right (hclose i) (by norm_num)
  have hy : (fun i => (x i + y i) / 2) ∈ shellKernelSupport k y := by
    intro i
    have he : (x i + y i) / 2 - y i = (x i - y i) / 2 := by ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_lt_div_of_pos_right (hclose i) (by norm_num)
  exact Set.disjoint_left.mp hxy hx hy

end ASDExplicitGamma.Model
