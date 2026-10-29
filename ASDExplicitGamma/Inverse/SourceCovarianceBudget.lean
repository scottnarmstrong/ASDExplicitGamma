module

public import ASDExplicitGamma.Inverse.SourceCovarianceCaps

/-! The complete source covariance sums control every variance-weighted finite band. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Variational
noncomputable section

private theorem source_weighted_partial_sum
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

/-- Sharp `K,M,Q` budgets for every finite band; the caps come from complete
series, so no cutoff or omitted-tail hypothesis is needed. -/
theorem source_covariance_weighted_partial_sums
    (S : Finset ℕ) (v : ℕ → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hv : ∀ i ∈ S, v i ≤ e) :
    (∑ i ∈ S, v i*lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i)) ≤
      (521/1000:ℝ)*e ∧
    (∑ i ∈ S, v i*pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)) ≤
      (1975/1000:ℝ)*e ∧
    (∑ i ∈ S, v i*((pureFluxCovarianceB 0 i)^2+
      lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i))) ≤
      (1565/1000:ℝ)*e := by
  have hk0 (i : ℕ) : 0 ≤ lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) := by
    have hρ := (pureFlux_covariance_rho_pos 0 i).le
    have hδ := (pureFlux_covariance_delta_bounds 0 i).1
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  refine ⟨?_,?_,?_⟩
  · exact source_weighted_partial_sum S v _ e _ he hv hk0 source_covariance_k_sum.1
      (source_covariance_k_sum.2.le.trans_eq (by norm_num))
  · exact source_weighted_partial_sum S v _ e _ he hv
      (fun _ => (pureFlux_covariance_mu_lower _ _).1) bank_covariance_plain_sum.1
      (bank_covariance_plain_sum.2.le.trans_eq (by norm_num))
  · exact source_weighted_partial_sum S v _ e _ he hv
      (fun i => add_nonneg (sq_nonneg _) (hk0 i)) source_covariance_q_sum.1
      (source_covariance_q_sum.2.le.trans_eq (by norm_num))

end
end ASDExplicitGamma.Inverse
