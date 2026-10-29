module

public import ASDExplicitGamma.Scalar.Lambda8GlobalOscillation

/-! Summable families of descendant oscillations for actual parent projections. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
open scoped BigOperators

noncomputable section

/-- A summable collection of actual parent-projection Hessian sources has a
summable collection of descendant oscillations, with the exact deterministic
parent-to-descendant scale factor. -/
theorem lambda8_parentProjection_family_oscillation_sq_le
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (Q : TriadicCube 2) (n : ℕ) (f : ι → Vec 2 → ℝ)
    (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (hdiv : ∀ i, dirichletWeakLaplacian (H i) =ᵐ[normalizedCubeMeasure Q] f i)
    (hf : Summable (fun i => energy Q (f i))) :
    Summable (fun i => descendantsAverage Q n (fun R =>
      hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec ((u i).toH1Function.grad x)) ^ 2)) ∧
    (∑' i, descendantsAverage Q n (fun R =>
      hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec ((u i).toH1Function.grad x)) ^ 2)) ≤
      (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
        ∑' i, energy Q (f i) := by
  let osc : ι → ℝ := fun i => descendantsAverage Q n (fun R =>
    hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
      (fun x => HilbertVec.ofVec ((u i).toH1Function.grad x)) ^ 2)
  let C : ℝ := cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hnonneg (i : ι) : 0 ≤ osc i := by
    dsimp [osc, descendantsAverage]
    positivity
  have hbound (i : ι) : osc i ≤ C * energy Q (f i) := by
    dsimp [osc, C]
    calc
      _ ≤ cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2 *
          energy Q (dirichletWeakLaplacian (H i)) :=
        lambda8_parentProjection_descendant_oscillation_sq_le Q n (u i) (H i)
      _ = cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2 * energy Q (f i) := by
        congr 1
        rw [energy_eq_integral_sq, energy_eq_integral_sq]
        apply integral_congr_ae
        filter_upwards [hdiv i] with x hx
        rw [hx]
  have hscaled : Summable (fun i => C * energy Q (f i)) := hf.mul_left C
  have hosc : Summable osc := hscaled.of_nonneg_of_le hnonneg hbound
  refine ⟨?_, ?_⟩
  · simpa only [osc] using hosc
  · calc
      (∑' i, descendantsAverage Q n (fun R =>
        hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
          (fun x => HilbertVec.ofVec ((u i).toH1Function.grad x)) ^ 2)) =
          ∑' i, osc i := by rfl
      _ ≤ ∑' i, C * energy Q (f i) := hosc.tsum_le_tsum hbound hscaled
      _ = C * ∑' i, energy Q (f i) := by rw [← tsum_mul_left]

end
end ASDExplicitGamma.Scalar
