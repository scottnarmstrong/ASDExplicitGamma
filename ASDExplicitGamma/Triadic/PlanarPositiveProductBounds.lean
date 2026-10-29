module

public import ASDExplicitGamma.Triadic.VectorPositiveMultiplier
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations

/-! Vector-valued Sobolev product bounds with explicit essential supremum caps and convergence. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem planarCoordinate_le_euclideanNorm (v : Fin 2 → ℝ) (i : Fin 2) : |v i| ≤ planarEuclideanNorm v := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun a _ => sq_nonneg (v a)) (Finset.mem_univ i))

 theorem planarRow_sq_le_frobenius_sq (A : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    (∑ j, (A i j)^2) ≤ (planarFrobeniusNorm A)^2 := by
  rw [planarFrobeniusNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun j _ => sq_nonneg (A a j)) (Finset.mem_univ i)

/-- The sharp planar vector product estimate, including the actual convergence clauses. -/
theorem vectorPositiveHaarNorm_mul_of_caps (Q : TriadicCube 2) (b : PlanarW1Infinity Q)
    (f : H1Function (openCubeSet Q)) {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value b x) ≤ M)
    (hDb : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative b x) ≤ D) :
    (∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q
      (cubeIncrement Q (k+1) (fun x => planarW1Value b x i*f.toFun x)))) ∧
    vectorPositiveHaarNorm Q (fun x i => planarW1Value b x i*f.toFun x) ≤
      M*positiveHaarNorm Q f.toFun+cubeScaleFactor Q*planarC1*D*Real.sqrt (energy Q f.toFun) := by
  have hPf := positiveHaarIncrementSeries_summable Q f.memL2_normalizedCubeMeasure f.grad_memL2_normalizedCubeMeasure f.hasWeakGradient
  have hAi (i : Fin 2) : ∀ᵐ x ∂normalizedCubeMeasure Q, |(b.component i).toFun x| ≤ M := by
    filter_upwards [hb] with x hx
    exact (planarCoordinate_le_euclideanNorm (planarW1Value b x) i).trans hx
  have hDi (i : Fin 2) : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ j, ((b.component i).grad x j)^2) ≤ D^2 := by
    filter_upwards [hDb] with x hx
    exact (planarRow_sq_le_frobenius_sq (planarW1Derivative b x) i).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2)
  have hi (i : Fin 2) := positiveHaar_mul_of_bounds Q (b.component i) (b.component_memLp_top i)
    (b.derivative_memLp_top i) f.memL2_normalizedCubeMeasure hPf hM hD (hAi i) (hDi i)
  refine ⟨fun i => (hi i).1, ?_⟩
  have h := vectorPositiveHaarNorm_mul_le Q b f
  have hc : 0 ≤ cubeScaleFactor Q*planarC1 := mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right (planarW1ValueLInf_le_of_bound b hM hb) (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (planarW1DerivativeFrobeniusLInf_le_of_bound b hD hDb) hc) (Real.sqrt_nonneg _)))

end
end ASDExplicitGamma.Triadic
