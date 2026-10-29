module

public import ASDExplicitGamma.Inverse.SourceChildCovarianceK

/-! Every finite variance-weighted refined-child band consumes the complete
shifted source covariance sums, including their entire tails. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Variational
noncomputable section

private theorem source_child_weighted_sum
    (S : Finset ℕ) (v a : ℕ → ℝ) (e A : ℝ)
    (he : 0 ≤ e) (hv : ∀ i ∈ S, v i ≤ e) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) (hA : (∑' i, a i) ≤ A) :
    (∑ i ∈ S, v i*a i) ≤ A*e := by
  calc
    _ ≤ ∑ i ∈ S, e*a i := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hv i hi) (ha i)
    _ = e*(∑ i ∈ S, a i) := (Finset.mul_sum _ _ _).symm
    _ ≤ e*(∑' i, a i) := mul_le_mul_of_nonneg_left (hs.sum_le_tsum S (fun i _ => ha i)) he
    _ ≤ e*A := mul_le_mul_of_nonneg_left hA he
    _ = A*e := mul_comm _ _

/-- Exact refined K and M budgets for every bounded finite physical band. -/
theorem source_child_covariance_weighted_partial_sums
    (S : Finset ℕ) (v : ℕ → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hv : ∀ i ∈ S, v i ≤ e) :
    (∑ i ∈ S, v i*lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i)) ≤
      (65399707/10^9:ℝ)*e ∧
    (∑ i ∈ S, v i*pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)) ≤
      (259713047/10^9:ℝ)*e := by
  have hk0 (i : ℕ) : 0 ≤ lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i) := by
    have hr := (pureFlux_covariance_rho_pos 1 i).le
    have hd := (pureFlux_covariance_delta_bounds 1 i).1
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  refine ⟨?_,?_⟩
  · exact source_child_weighted_sum S v _ e _ he hv hk0 source_child_covariance_k_sum.1
      source_child_covariance_k_sum.2.le
  · exact source_child_weighted_sum S v _ e _ he hv
      (fun _ => (pureFlux_covariance_mu_lower _ _).1) source_child_covariance_plain_sum.1
      source_child_covariance_plain_sum.2.le

/-- The squared bracket budget follows from the same complete feedback and
deterministic sums; this auxiliary p20 comparison overpays by `M+K`. -/
theorem source_child_covariance_q_weighted_sum
    (S : Finset ℕ) (v : ℕ → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hv : ∀ i ∈ S, v i ≤ e) (hv0 : ∀ i ∈ S, 0 ≤ v i) :
    (∑ i ∈ S, v i*((pureFluxCovarianceB 1 i)^2+
      lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i))) ≤
      ((259713047/10^9:ℝ)+(65399707/10^9:ℝ))*e := by
  have hsums := source_child_covariance_weighted_partial_sums S v e he hv
  have hB (i : ℕ) : (pureFluxCovarianceB 1 i)^2 ≤
      pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i) :=
    (pow_le_pow_left₀ (pureFlux_covariance_rows_order 1 i).1
      (pureFlux_covariance_rows_order 1 i).2 2).trans (pureFlux_covariance_mu_lower _ _).2
  calc
    _ ≤ ∑ i ∈ S, v i*(pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)+
        lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i)) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (add_le_add (hB i) le_rfl) (hv0 i hi)
    _ = (∑ i ∈ S, v i*pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i))+
        ∑ i ∈ S, v i*lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ _ := (add_le_add hsums.2 hsums.1).trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
