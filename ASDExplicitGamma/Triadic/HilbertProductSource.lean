module

public import ASDExplicitGamma.Triadic.HilbertProduct
public import ASDExplicitGamma.Triadic.HilbertOperatorNorms
public import ASDExplicitGamma.Triadic.PlanarProductPoincare

/-! The source product theorem with literal essential suprema and exact fractional weight. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

/-- TR-PRODUCT at q=3^(2s), including actual membership of the product.
The planar zero-trace refinement is `planar_product_poincare`. -/
theorem hilbert_positive_product {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) (s : ℝ) (hs : 0 < s ∧ s < 1)
    {f : Vec d → E} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => ((3:ℝ)^(2*s))^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) f))) :
    let q := (3:ℝ)^(2*s)
    Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) (fun x => b.toFun x (f x)))) ∧
    hilbertPositiveHaarNorm Q q (fun x => b.toFun x (f x)) ≤ b.valueLInf*hilbertPositiveHaarNorm Q q f+
      cubeScaleFactor Q*Real.sqrt (haarPoincareM2 q)*b.derivativeFrobeniusLInf*hilbertL2Norm Q f := by
  have hq : 1 < (3:ℝ)^(2*s) := Real.one_lt_rpow (by norm_num) (mul_pos (by norm_num) hs.1)
  have hq9 : (3:ℝ)^(2*s) < 9 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<3) (show 2*s < 2 by linarith only [hs.2])
    norm_num at h ⊢
    exact h
  exact hilbert_positive_product_of_bounds b hq hq9 hf hP lpNorm_nonneg lpNorm_nonneg
    b.ae_value_le b.ae_gradient_sq_le

end
end ASDExplicitGamma.Triadic
