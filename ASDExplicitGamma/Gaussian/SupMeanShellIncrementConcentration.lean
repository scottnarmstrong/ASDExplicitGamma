module

public import ASDExplicitGamma.Gaussian.SupMeanShellProjectionIncrement

/-! Sharp centered tensor-increment MGF under the actual frozen shell law. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- Gradient increments have the sharp ell_2 centered MGF, with integrability
proved internally from their actual joint Gaussian law and covariance. -/
theorem supMean_shell_first_increment_mgf (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x y : Vec 2) (lam : ℝ) :
    let X := fun (i : Fin 2) j => supMeanShellJetScalar (.first i) y j-supMeanShellJetScalar (.first i) x j
    Integrable (fun j => Real.exp (lam*(supMeanTensorNorm X j-
      ∫ z, supMeanTensorNorm X z ∂(ShellField.shellMarginalLaw M.P k).toMeasure)))
        (ShellField.shellMarginalLaw M.P k).toMeasure ∧
    (∫ j, Real.exp (lam*(supMeanTensorNorm X j-
      ∫ z, supMeanTensorNorm X z ∂(ShellField.shellMarginalLaw M.P k).toMeasure))
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.exp (lam^2*((waveEll2^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4))*
          ((y-x) 0^2+(y-x) 1^2))/2) := by
  intro X
  let B := (waveEll2^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4))*((y-x) 0^2+(y-x) 1^2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let C := Real.sqrt B
  have hCsq : C^2 = B := Real.sq_sqrt hB
  have hg : IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure X :=
    supMean_gaussian_difference_family (supMean_shell_jets_gaussian M h hM k)
      (fun i : Fin 2 => (Q3SpatialJet.first i,y)) (fun i : Fin 2 => (Q3SpatialJet.first i,x))
  have hv (a : Fin 2 → ℝ) : Var[(fun j => ∑ i, a i*X i j);
      (ShellField.shellMarginalLaw M.P k).toMeasure] ≤ C^2*(∑ i, a i^2) := by
    calc
      _ ≤ (waveEll2^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4))*(∑ i, a i^2)*
          ((y-x) 0^2+(y-x) 1^2) := supMean_shell_first_projection_increment M h hM k a x y
      _ = _ := by rw [hCsq]; dsimp only [B]; ring
  have hh := supMean_gaussian_tensor_mgf (ShellField.shellMarginalLaw M.P k).toMeasure X hg C lam
    (Real.sqrt_nonneg _) hv
  simpa only [hCsq, B] using hh

/-- The stored Hessian increments have the sharp ell_3 centered MGF. The proof
uses the genuine third weak kernel and assumes no C3 random-shell domain. -/
theorem supMean_shell_second_increment_mgf (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (x y : Vec 2) (lam : ℝ) :
    let X := fun (i : Fin 2 × Fin 2) j => supMeanShellJetScalar (.second i.1 i.2) y j-
      supMeanShellJetScalar (.second i.1 i.2) x j
    Integrable (fun j => Real.exp (lam*(supMeanTensorNorm X j-
      ∫ z, supMeanTensorNorm X z ∂(ShellField.shellMarginalLaw M.P k).toMeasure)))
        (ShellField.shellMarginalLaw M.P k).toMeasure ∧
    (∫ j, Real.exp (lam*(supMeanTensorNorm X j-
      ∫ z, supMeanTensorNorm X z ∂(ShellField.shellMarginalLaw M.P k).toMeasure))
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.exp (lam^2*((waveEll3^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6))*
          ((y-x) 0^2+(y-x) 1^2))/2) := by
  intro X
  let B := (waveEll3^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6))*((y-x) 0^2+(y-x) 1^2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let C := Real.sqrt B
  have hCsq : C^2 = B := Real.sq_sqrt hB
  have hg : IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure X :=
    supMean_gaussian_difference_family (supMean_shell_jets_gaussian M h hM k)
      (fun i : Fin 2 × Fin 2 => (Q3SpatialJet.second i.1 i.2,y))
      (fun i : Fin 2 × Fin 2 => (Q3SpatialJet.second i.1 i.2,x))
  have hv (a : Fin 2 × Fin 2 → ℝ) : Var[(fun j => ∑ i, a i*X i j);
      (ShellField.shellMarginalLaw M.P k).toMeasure] ≤ C^2*(∑ i, a i^2) := by
    calc
      _ ≤ (waveEll3^2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6))*(∑ i, a i^2)*
          ((y-x) 0^2+(y-x) 1^2) := supMean_shell_second_projection_increment M h hM k a x y
      _ = _ := by rw [hCsq]; dsimp only [B]; ring
  have hh := supMean_gaussian_tensor_mgf (ShellField.shellMarginalLaw M.P k).toMeasure X hg C lam
    (Real.sqrt_nonneg _) hv
  simpa only [hCsq, B] using hh

end
end ASDExplicitGamma.Gaussian
