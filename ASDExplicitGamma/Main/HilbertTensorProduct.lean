module

public import ASDExplicitGamma.Main.EuclideanTensor
public import ASDExplicitGamma.Main.SmoothHilbertOperator

/-! Actual finite Hilbert-column tensor multipliers with source product constants. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

/-- Differentiation of the literal tensor coefficient map. -/
theorem main_tensor_map_fderiv {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (b : Vec 2 → EuclideanSpace ℝ κ) (hb : ContDiff ℝ 1 b) (x : Vec 2) (i : Fin 2) :
    (fderiv ℝ (fun y => mainEuclideanTensorMap (κ := κ) (ρ := ρ) (b y)) x) (basisVec i) =
      mainEuclideanTensorOperator ((fderiv ℝ b x) (basisVec i)) := by
  let T := mainEuclideanTensorMap (κ := κ) (ρ := ρ)
  have h := T.hasFDerivAt.comp x
    ((hb.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  exact congrArg (fun D : Vec 2 →L[ℝ] (EuclideanSpace ℝ ρ →L[ℝ] EuclideanSpace ℝ (κ × ρ)) =>
    D (basisVec i)) h.fderiv

/-- An actual Hilbert column times an arbitrary vector field obeys the
operator product bound. Both essential-supremum bounds concern the column
Hilbert norm, with no sum over the input vector coordinates. -/
theorem main_hilbert_tensor_product {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (Q : TriadicCube 2) (b : Vec 2 → EuclideanSpace ℝ κ) (hb : ContDiff ℝ 1 b)
    {f : Vec 2 → EuclideanSpace ℝ ρ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) f)))
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hm : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b x‖ ≤ M)
    (hd : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i, ‖(fderiv ℝ b x) (basisVec i)‖^2) ≤ D^2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => mainEuclideanTensor (b x) (f x)))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => mainEuclideanTensor (b x) (f x)) ≤
      M*hilbertPositiveHaarNorm Q (Real.sqrt 3) f+
        cubeScaleFactor Q*planarC1*D*hilbertL2Norm Q f := by
  let T := mainEuclideanTensorMap (κ := κ) (ρ := ρ)
  let B := mainSmoothHilbertOperator Q (fun x => T (b x)) (T.contDiff.comp hb)
  have hm' : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖B.toFun x‖ ≤ M := by
    filter_upwards [hm] with x hx
    exact (mainEuclideanTensorOperator_norm_le (ρ := ρ) (b x)).trans hx
  have hd' : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖B.grad x i‖^2) ≤ D^2 := by
    filter_upwards [hd] with x hx
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hx
    change ‖(fderiv ℝ (fun y => T (b y)) x) (basisVec i)‖^2 ≤ _
    rw [main_tensor_map_fderiv b hb]
    exact pow_le_pow_left₀ (norm_nonneg _) (mainEuclideanTensorOperator_norm_le (ρ := ρ) _) 2
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have h := hilbert_positive_product_of_bounds B hq hq9 hf hP hM hD hm' hd'
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  have heq : (fun x => B.toFun x (f x)) =
      (fun x => mainEuclideanTensor (b x) (f x)) := rfl
  simpa only [heq, hc1] using h

end ASDExplicitGamma.Main
