module

public import ASDExplicitGamma.Main.RankOneMultiplier
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge

/-! Hilbert-valued column products with zero-trace scalar inputs. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

/-- The positive-Haar product estimate for an actual smooth Hilbert column.
The derivative cap is the spatial Frobenius cap, with no coordinate loss. -/
theorem main_hilbert_column_product {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    (b : Vec 2 → F) (hb : ContDiff ℝ 1 b)
    (u : H1Function (openCubeSet Q)) {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hm : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b x‖ ≤ M)
    (hd : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i, ‖(fderiv ℝ b x) (basisVec i)‖^2) ≤ D^2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => u.toFun x • b x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => u.toFun x • b x) ≤
      M*positiveHaarNorm Q u.toFun +
        cubeScaleFactor Q*planarC1*D*Real.sqrt (energy Q u.toFun) := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hp := positiveHaarIncrementSeries_summable Q u.memL2_normalizedCubeMeasure
    u.grad_memL2_normalizedCubeMeasure u.hasWeakGradient
  have hpH : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) u.toFun)) := by
    simpa only [hilbertCubeIncrement_real, hilbertEnergy_real] using hp
  have hm' : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ‖(mainRankOneMultiplier Q b hb).toFun x‖ ≤ M := by
    simpa only [mainRankOneMultiplier_norm] using hm
  have hd' : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i, ‖(mainRankOneMultiplier Q b hb).grad x i‖^2) ≤ D^2 := by
    simpa only [mainRankOneMultiplier_gradient_norm] using hd
  have h := hilbert_positive_product_of_bounds (mainRankOneMultiplier Q b hb)
    hq hq9 u.memL2_normalizedCubeMeasure hpH hM hD hm' hd'
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  simpa only [mainRankOneMultiplier, ContinuousLinearMap.toSpanSingleton_apply,
    hilbertPositiveHaarNorm, hilbertPrimalEnergy_real, positiveHaarNorm,
    hilbertL2Norm, hilbertEnergy_real, hc1] using h

/-- The exact Dirichlet improvement for Hilbert column products. The
zero-trace bridges are proved internally, rather than assumed estimates. -/
theorem main_hilbert_column_dirichlet {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    (b : Vec 2 → F) (hb : ContDiff ℝ 1 b)
    (u : H10Function (openCubeSet Q)) {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hm : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b x‖ ≤ M)
    (hd : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∑ i, ‖(fderiv ℝ b x) (basisVec i)‖^2) ≤ D^2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => u.toH1Function.toFun x • b x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => u.toH1Function.toFun x • b x) ≤
      (cubeScaleFactor Q*planarFD*M + cubeScaleFactor Q^2*planarCD*planarC1*D)*
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  obtain ⟨hs, he⟩ := main_hilbert_column_product Q b hb u.toH1Function hM hD hm hd
  refine ⟨hs, he.trans ?_⟩
  calc
    _ ≤ M*(cubeScaleFactor Q*planarFD*
          vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i)) +
        cubeScaleFactor Q*planarC1*D*(cubeScaleFactor Q*planarCD*
          vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i)) :=
      add_le_add (mul_le_mul_of_nonneg_left (dirichlet_positiveHaar_bridge Q u) hM)
        (mul_le_mul_of_nonneg_left (dirichlet_L2_bridge Q u)
          (mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)) hD))
    _ = _ := by ring

end ASDExplicitGamma.Main
