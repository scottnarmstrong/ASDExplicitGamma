module

public import ASDExplicitGamma.Gaussian.Q3RealizationLaw
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.LinearAlgebra.Pi

/-! # The frozen product-q3 stream is a genuine Gaussian process -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Every linear functional on a finite real coordinate family is its literal coordinate sum. -/
theorem cold_linear_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, L (Pi.single i 1)*v i := by
  have he : v = ∑ i, v i • Pi.single i 1 := by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  calc
    L v = L (∑ i, v i • Pi.single i 1) := congrArg L he
    _ = ∑ i, L (Pi.single i 1)*v i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,smul_eq_mul,mul_comm]

/-- The exact author-frozen finite-observation assumption yields joint Gaussianity
of all point-stream observations. -/
theorem cold_zeroShell_isGaussianProcess (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) :
    IsGaussianProcess (fun x : Vec 2 => fun j : ShellField 2 => j x 1 0)
      (ShellField.zeroShellLaw M.P).toMeasure := by
  classical
  constructor
  intro I
  let X := fun (j : ShellField 2) (i : I) => j i.val 1 0
  change HasGaussianLaw X (ShellField.zeroShellLaw M.P).toMeasure
  have hX : Measurable X := measurable_pi_iff.mpr (fun i => ShellField.measurable_eval_entry i.val 1 0)
  refine ⟨hX.aemeasurable,?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  rw [Measure.map_map L.measurable hX]
  have he : (L ∘ X) = (fun j => ∑ i : I, L (Pi.single i 1)*j i.val 1 0) := by
    funext j
    exact cold_linear_pi_sum L (X j)
  rw [he]
  have hobs := Gaussian.zeroShellLaw_map_finite_q3_observation M h hM
    (K := Set.univ) (x := fun i : I => ⟨i.val,Set.mem_univ _⟩) (t := fun i => L (Pi.single i 1))
  exact ⟨0,_,hobs⟩

end ASDExplicitGamma.Cold
