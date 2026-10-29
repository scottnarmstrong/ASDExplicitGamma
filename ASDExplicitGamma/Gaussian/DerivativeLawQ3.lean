module

public import ASDExplicitGamma.Gaussian.DerivativeLawStored
public import ASDExplicitGamma.Model.Q3DerivativeMoments

/-! The actual finite joint Gaussian law of all stored q3 shell derivatives at every level. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section

/-- The scaled product-q3 covariance kernel at the exact integer shell level. -/
def q3ShellCovariance (M : ABKModel 2) (h : ℝ) (k : ℤ) (x y : Vec 2) : ℝ :=
  h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))*q3Cov (((3:ℝ)^k)⁻¹*(x-y) 0)*q3Cov (((3:ℝ)^k)⁻¹*(x-y) 1)

 theorem q3Shell_values_gaussian (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure (fun x j => shellScalarValue j x) := by
  classical
  constructor
  · intro x
    exact (shellDerivativeEval_continuous (.value x)).measurable.aemeasurable
  · intro J _ x t
    let n := Fintype.card J
    let e : Fin n ≃ J := (Fintype.equivFin J).symm
    have hfin : ∃ v : NNReal, (ShellField.shellMarginalLaw M.P k).toMeasure.map
        (ASDExplicitGamma.Model.shellStreamObservable n (fun i => x (e i)) (fun i => t (e i))) = gaussianReal 0 v :=
      ⟨_, ASDExplicitGamma.Model.shellStream_linearCombination_law M h hM k n (fun i => x (e i)) (fun i => t (e i))⟩
    obtain ⟨v,hv⟩ := hfin
    refine ⟨v, ?_⟩
    rw [← hv]
    congr 1
    funext j
    change (∑ i : J, t i*j (x i) 1 0) = ∑ i : Fin n, t (e i)*j (x (e i)) 1 0
    exact (Equiv.sum_comp e (fun i => t i*j (x i) 1 0)).symm

/-- GA-DERIVATIVE-LAW joint Gaussianity clause, for literal frozen C2 data,
all finite mixed value/first/second observations, and every integer shell level. -/
theorem q3Shell_stored_derivatives_gaussian (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure shellDerivativeEval :=
  isCenteredGaussianFamily_stored_derivatives _ (q3Shell_values_gaussian M h hM k)

end
end ASDExplicitGamma.Gaussian
