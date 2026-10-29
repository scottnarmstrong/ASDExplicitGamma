module

public import ASDExplicitGamma.Triadic.HilbertOperatorOscillation

/-! The sharp residual estimate for genuine operator-valued Sobolev multipliers. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

/-- The operator product residual separates into the input residual and a cell oscillation. -/
theorem hilbert_operator_product_residual_le {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) (j : ℕ) {f : Vec d → E} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b.toFun x‖ ≤ B)
    (hdb : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖b.grad x i‖^2) ≤ D^2) :
    hilbertL2Norm Q (fun x => b.toFun x (f x)-hilbertCubeProjection Q j (fun y => b.toFun y (f y)) x) ≤
      B*hilbertL2Norm Q (fun x => f x-hilbertCubeProjection Q j f x)+
      cubeScaleFactor Q/((3:ℝ)^j*Real.pi)*D*hilbertL2Norm Q f := by
  let A := fun x => b.toFun x (f x-hilbertCubeProjection Q j f x)
  let v := fun x => b.toFun x (hilbertCubeProjection Q j f x)
  have hA : MemLp A 2 (normalizedCubeMeasure Q) := b.product_memLp (hf.sub (hilbertCubeProjection_memLp Q j f 2))
  have hv : MemLp v 2 (normalizedCubeMeasure Q) := b.product_memLp (hilbertCubeProjection_memLp Q j f 2)
  have heq : (fun x => b.toFun x (f x)) = fun x => A x+v x := by
    funext x
    dsimp [A, v]
    rw [map_sub, sub_add_cancel]
  have hr : (fun x => b.toFun x (f x)-hilbertCubeProjection Q j (fun y => b.toFun y (f y)) x) =
      fun x => (A x-hilbertCubeProjection Q j A x)+(v x-hilbertCubeProjection Q j v x) := by
    rw [heq, hilbertCubeProjection_add Q j hA hv]
    funext x
    rw [congrFun heq x]
    exact (sub_add_sub_comm _ _ _ _).symm
  have htri := hilbertL2Norm_add_le Q (hA.sub (hilbertCubeProjection_memLp Q j A 2))
    (hv.sub (hilbertCubeProjection_memLp Q j v 2))
  have hAenergy := hilbert_operator_product_energy_le Q hB hb (hf.sub (hilbertCubeProjection_memLp Q j f 2)) hA
  have hAnorm : hilbertL2Norm Q (fun x => A x-hilbertCubeProjection Q j A x) ≤
      B*hilbertL2Norm Q (fun x => f x-hilbertCubeProjection Q j f x) := by
    have h := Real.sqrt_le_sqrt ((hilbertEnergy_residual_le Q j hA).trans hAenergy)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB] at h
    exact h
  have hvnorm : hilbertL2Norm Q (fun x => v x-hilbertCubeProjection Q j v x) ≤
      cubeScaleFactor Q/((3:ℝ)^j*Real.pi)*D*hilbertL2Norm Q f := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (mul_nonneg (div_nonneg (cubeScaleFactor_pos' Q).le (by positivity)) hD) (Real.sqrt_nonneg _), ?_⟩
    have h := hilbert_operator_mean_oscillation_energy_le b j hf hdb
    refine h.trans_eq ?_
    change _ = (cubeScaleFactor Q/((3:ℝ)^j*Real.pi)*D*Real.sqrt (hilbertEnergy Q f))^2
    rw [mul_pow, mul_pow, Real.sq_sqrt (hilbertEnergy_nonneg Q f), div_pow, mul_pow]
    have h9 : ((3:ℝ)^j)^2 = (9:ℝ)^j := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul]; norm_num
    rw [h9]
  rw [hr]
  exact htri.trans (add_le_add hAnorm hvnorm)

end
end ASDExplicitGamma.Triadic
