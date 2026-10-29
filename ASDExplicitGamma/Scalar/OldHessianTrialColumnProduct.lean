module

public import ASDExplicitGamma.Main.Q3ColumnHilbertSchmidt
public import ASDExplicitGamma.Native.OldSignedDerivativeRowNumeric

/-! The actual coarse product column, retaining its full Frobenius factor
sqrt(2). The derivative-only row coefficient is not reused as a column cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian
noncomputable section

/-- The full column has twice the row variances. The sharp Dirichlet
constants bound its coefficient at the actual cell side and physical length. -/
theorem old_hessian_column_coefficient {R : ℝ} (hR : 0≤R) (b L : ℝ) :
    R*planarFD*Real.sqrt ((156/5)*b^2/L^2)+
      R^2*planarCD*planarC1*Real.sqrt ((46488/25)*b^2/L^4) ≤
      oldSignedDerivativeKappa R (Real.sqrt 2*b) L := by
  have hb : (Real.sqrt 2*b)^2=2*b^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have he : oldSignedDerivativeRowCoefficient R (Real.sqrt 2*b) L =
      R*planarFD*Real.sqrt ((156/5)*b^2/L^2)+
        R^2*planarCD*planarC1*Real.sqrt ((46488/25)*b^2/L^4) := by
    unfold oldSignedDerivativeRowCoefficient
    rw [hb]
    congr 2 <;> congr 1 <;> ring
  rw [←he]
  exact old_signed_derivative_row_coefficient_le_kappa hR _ _

/-- The outward column polynomial is sqrt(2) times the row polynomial,
evaluated at the actual (coarse) cell side divided by the shell length. -/
theorem old_hessian_column_polynomial {R : ℝ} (hR : 0≤R) (b L : ℝ) (hL : 0<L) :
    oldSignedDerivativeKappa R (Real.sqrt 2*b) L ≤
      Real.sqrt 2*((503/200:ℝ)*(R/L)+(2031/500:ℝ)*(R/L)^2)*|b| := by
  rw [old_signed_derivative_kappa_shape R _ L hL,abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hh := mul_le_mul_of_nonneg_right
    (old_signed_derivative_shape_polynomial (div_nonneg hR hL.le))
    (mul_nonneg (Real.sqrt_nonneg (2:ℝ)) (abs_nonneg b))
  exact hh.trans_eq (by ring)

/-- Finite actual Gaussian product columns have the sharp full-column cap,
with genuine convergence of every positive Haar depth. -/
theorem old_hessian_finite_column_product {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0<l}) (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (j+1) (fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3)
      (fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x) ≤
      oldSignedDerivativeKappa (cubeScaleFactor Q) (Real.sqrt 2*b) L.1*
        vectorWeakHaarNorm Q u.toH1Function.grad := by
  have hh := main_hilbert_column_dirichlet Q _ (mainQ3FiniteColumn_contDiff e s b L) u
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall (fun x =>
      (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (mainQ3FiniteColumn_norm_sq_le e s b L x)))
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.sq_sqrt (by positivity : 0≤(46488/25:ℝ)*b^2/L.1^4)]
      exact mainQ3FiniteColumn_derivative_sq_le e s b L x))
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right
    (old_hessian_column_coefficient (Triadic.cubeScaleFactor_pos' Q).le b L.1) (Real.sqrt_nonneg _))⟩

/-- Every finite family is bounded before taking the complete white sum. -/
theorem old_hessian_column_energy_finset {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0<l}) (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    (∑ j ∈ s,mainQ3DerivativeColumnEnergy e Q b L u j) ≤
      (oldSignedDerivativeKappa (cubeScaleFactor Q) (Real.sqrt 2*b) L.1*
        vectorWeakHaarNorm Q u.toH1Function.grad)^2 := by
  let F := fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x
  have hF : MemLp F 2 (normalizedCubeMeasure Q) :=
    (mainRankOneMultiplier Q _ (mainQ3FiniteColumn_contDiff e s b L)).product_memLp
      u.toH1Function.memL2_normalizedCubeMeasure
  obtain ⟨hP,he⟩ := old_hessian_finite_column_product e s b L Q u
  have hE : hilbertPrimalEnergy Q (Real.sqrt 3) F =
      ∑ j ∈ s,mainQ3DerivativeColumnEnergy e Q b L u j := by
    rw [main_hilbertPrimalEnergy_euclidean Q hF hP]
    simp only [F,mainQ3FiniteColumn,PiLp.smul_apply,smul_eq_mul,Fintype.sum_prod_type,
      mainQ3DerivativeColumnEnergy]
    exact Finset.sum_coe_sort s (mainQ3DerivativeColumnEnergy e Q b L u)
  have hn : 0≤hilbertPrimalEnergy Q (Real.sqrt 3) F := by
    unfold hilbertPrimalEnergy
    exact add_nonneg (hilbertEnergy_nonneg Q _) (tsum_nonneg (fun j =>
      mul_nonneg (by positivity) (hilbertEnergy_nonneg Q _)))
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) he 2
  change (Real.sqrt (hilbertPrimalEnergy Q (Real.sqrt 3) F))^2≤_ at hb
  rwa [Real.sq_sqrt hn,hE] at hb

/-- The entire physical column family is summable and has the same cap.
This is the coarse source product, with no Gaussian finite-rank hypothesis. -/
theorem old_hessian_column_energy {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0<l}) (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    Summable (mainQ3DerivativeColumnEnergy e Q b L u) ∧
    (∑' j,mainQ3DerivativeColumnEnergy e Q b L u j) ≤
      (oldSignedDerivativeKappa (cubeScaleFactor Q) (Real.sqrt 2*b) L.1*
        vectorWeakHaarNorm Q u.toH1Function.grad)^2 := by
  have hn (j : I) : 0≤mainQ3DerivativeColumnEnergy e Q b L u j :=
    Finset.sum_nonneg (fun i _ => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)
  have hb := fun s => old_hessian_column_energy_finset e s b L Q u
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

end
end ASDExplicitGamma.Scalar
