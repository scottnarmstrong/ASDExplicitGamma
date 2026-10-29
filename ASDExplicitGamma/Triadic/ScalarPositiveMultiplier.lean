module

public import ASDExplicitGamma.Triadic.HilbertProduct
public import ASDExplicitGamma.Triadic.PlanarSobolev
public import Mathlib.Analysis.Normed.Operator.Mul
public import Homogenization.Sobolev.H1.Algebra.H1Function

/-! Scalar Sobolev multipliers acting on arbitrary positive-Haar inputs. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- The scalar multiplication map with its real operator space fixed explicitly. -/
def scalarMultiplicationCLM : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ

/-- Scalar multiplication as a genuine operator-valued weak Sobolev field. -/
def scalarSobolevOperator {d : ℕ} (Q : TriadicCube d) (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (normalizedCubeMeasure Q))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (normalizedCubeMeasure Q)) : HilbertOperatorW1Infinity Q ℝ ℝ where
  toFun x := scalarMultiplicationCLM (η.toFun x)
  grad x i := scalarMultiplicationCLM (η.grad x i)
  memLp_top := (scalarMultiplicationCLM).comp_memLp' hη
  gradMemLp_top i := (scalarMultiplicationCLM).comp_memLp' (hDη i)
  hasWeakGradient e v := by
    have hf : (fun x => inner ℝ v (scalarMultiplicationCLM (η.toFun x) e)) = ((v*e) • η).toFun := by
      funext x
      simp only [scalarMultiplicationCLM, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.inner_apply, H1Function.smul_toFun]
      ring
    have hg : (fun x i => inner ℝ v (scalarMultiplicationCLM (η.grad x i) e)) = ((v*e) • η).grad := by
      funext x i
      simp only [scalarMultiplicationCLM, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.inner_apply, H1Function.smul_grad, Pi.smul_apply]
      ring
    rw [hf, hg]
    exact ((v*e) • η).hasWeakGradient

/-- Exact scalar multiplier bound with actual positive-series membership of the product. -/
theorem positiveHaar_mul_of_bounds {d : ℕ} (Q : TriadicCube d) (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (normalizedCubeMeasure Q))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (normalizedCubeMeasure Q))
    {f : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) f)))
    {A G : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.toFun x| ≤ A)
    (hg : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, (η.grad x i)^2) ≤ G^2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => η.toFun x*f x))) ∧
    positiveHaarNorm Q (fun x => η.toFun x*f x) ≤ A*positiveHaarNorm Q f+
      cubeScaleFactor Q*planarC1*G*Real.sqrt (energy Q f) := by
  let b := scalarSobolevOperator Q η hη hDη
  have hq : 1 < Real.sqrt 3 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3 < 9 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hbn : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b.toFun x‖ ≤ A := by
    filter_upwards [hb] with x hx
    simpa only [b, scalarSobolevOperator, scalarMultiplicationCLM, ContinuousLinearMap.opNorm_lsmul_apply, Real.norm_eq_abs] using hx
  have hgn : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖b.grad x i‖^2) ≤ G^2 := by
    filter_upwards [hg] with x hx
    simpa only [b, scalarSobolevOperator, scalarMultiplicationCLM, ContinuousLinearMap.opNorm_lsmul_apply, Real.norm_eq_abs, sq_abs] using hx
  have hpH : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) f)) := by
    simpa only [hilbertCubeIncrement_real, hilbertEnergy_real] using hP
  have h := hilbert_positive_product_of_bounds b hq hq9 hf hpH hA hG hbn hgn
  have heq : (fun x => b.toFun x (f x)) = fun x => η.toFun x*f x := by funext x; rfl
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  simpa only [heq, hilbertCubeIncrement_real, hilbertEnergy_real, hilbertPositiveHaarNorm,
    hilbertPrimalEnergy_real, positiveHaarNorm, hilbertL2Norm, hc1] using h

end
end ASDExplicitGamma.Triadic
