module

public import ASDExplicitGamma.Triadic.PlanarPositiveProductBounds
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! The exact deterministic positive-Haar bound for the planar lifted row field. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

/-- The lifted row in scalar skew coordinates; the minus sign is column divergence. -/
def planarRowProduct {Q : TriadicCube 2} (η : PlanarW2Infinity Q) (F : Vec 2 → Fin 2 → ℝ)
    (r : H1Function (openCubeSet Q)) : Vec 2 → Fin 2 → ℝ :=
  fun x => planarQuarterTurn (fun i => η.value.toFun x*F x i-η.value.grad x i*r.toFun x)

/-- The row product estimate for an arbitrary positive field and a genuine H1 residual. -/
theorem planarRowProduct_bound (Q : TriadicCube 2) (η : PlanarW2Infinity Q) (F : Vec 2 → Fin 2 → ℝ)
    (r : H1Function (openCubeSet Q)) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hP : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i))))
    {A G H : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hval : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.value.toFun x| ≤ A)
    (hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value η.gradient x) ≤ G)
    (hhess : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative η.gradient x) ≤ H) :
    (∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => planarRowProduct η F r x i)))) ∧
    vectorPositiveHaarNorm Q (planarRowProduct η F r) ≤
      (A+cubeScaleFactor Q*planarC1*G)*vectorPositiveHaarNorm Q F+
      G*positiveHaarNorm Q r.toFun+cubeScaleFactor Q*planarC1*H*Real.sqrt (energy Q r.toFun) := by
  let AF := fun x i => η.value.toFun x*F x i
  let b := η.gradient.neg
  let BF := fun x i => planarW1Value b x i*r.toFun x
  have hgsq : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, (η.value.grad x i)^2) ≤ G^2 := by
    filter_upwards [hgrad] with x hx
    have h : (planarEuclideanNorm (planarW1Value η.gradient x))^2 ≤ G^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    rw [planarEuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
    simpa only [planarW1Value, η.gradient_eq] using h
  have hAF := vectorPositiveHaar_mul_of_bounds Q η.value η.value_memLp_top_normalized
    η.grad_memLp_top_normalized F hF hP hA hG hval hgsq
  have hb : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value b x) ≤ G := by
    filter_upwards [hgrad] with x hx
    simpa only [b, PlanarW1Infinity.neg, planarW1Value, H1Function.neg_toFun, planarEuclideanNorm, neg_sq] using hx
  have hDb : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative b x) ≤ H := by
    filter_upwards [hhess] with x hx
    simpa only [b, PlanarW1Infinity.neg, planarW1Derivative, H1Function.neg_grad, Pi.neg_apply, planarFrobeniusNorm, neg_sq] using hx
  have hBF := vectorPositiveHaarNorm_mul_of_caps Q b r hG hH hb hDb
  have hAFmem (i : Fin 2) : MemLp (fun x => AF x i) 2 (normalizedCubeMeasure Q) :=
    η.value_memLp_top_normalized.mul (hF i)
  have hBFmem (i : Fin 2) : MemLp (fun x => BF x i) 2 (normalizedCubeMeasure Q) :=
    (b.component_memLp_top i).mul r.memL2_normalizedCubeMeasure
  have hadd := vectorPositiveHaar_add_le Q AF BF hAFmem hBFmem hAF.1 hBF.1
  have heq : planarRowProduct η F r = fun x => planarQuarterTurn (fun i => AF x i+BF x i) := by
    funext x
    apply congrArg planarQuarterTurn
    funext i
    simp only [AF, BF, b, planarW1Value, PlanarW1Infinity.neg, H1Function.neg_toFun, η.gradient_eq]
    ring
  have hRCG : 0 ≤ cubeScaleFactor Q*planarC1*G := mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)) hG
  have hAFbound : vectorPositiveHaarNorm Q AF ≤ (A+cubeScaleFactor Q*planarC1*G)*vectorPositiveHaarNorm Q F := by
    calc
      _ ≤ A*vectorPositiveHaarNorm Q F+cubeScaleFactor Q*planarC1*G*Real.sqrt (∑ i, energy Q (fun x => F x i)) := hAF.2
      _ ≤ A*vectorPositiveHaarNorm Q F+cubeScaleFactor Q*planarC1*G*vectorPositiveHaarNorm Q F :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (vectorL2_le_vectorPositiveHaar Q F hF hP) hRCG)
      _ = _ := by ring
  rw [heq]
  refine ⟨positive_series_quarterTurn Q _ hadd.1, ?_⟩
  rw [vectorPositiveHaarNorm_quarterTurn]
  exact hadd.2.trans (by linarith only [hAFbound, hBF.2])

end
end ASDExplicitGamma.Triadic
