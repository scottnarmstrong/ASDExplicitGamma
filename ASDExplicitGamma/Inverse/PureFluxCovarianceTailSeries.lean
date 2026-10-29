module

public import ASDExplicitGamma.Inverse.PureFluxCovarianceMajorants
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Complete all-shell covariance tails for the source feedback coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Exact complete rho^m tail, with both source shift and starting shell. -/
theorem pureFlux_covariance_rho_power_hasSum (q first m : ℕ) (hm : 0 < m) :
    HasSum (fun n : ℕ => (pureFluxCovarianceRho q (first+n))^m)
      ((1/3:ℝ)^(m*(q+first+1))/(1-(1/3:ℝ)^m)) := by
  have hr : (1/3:ℝ)^m < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hm.ne'
  have hh := (hasSum_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (1/3:ℝ)^m) hr).mul_left
    ((1/3:ℝ)^(m*(q+first+1)))
  convert hh using 1
  · funext n
    unfold pureFluxCovarianceRho
    rw [← pow_mul,show (q+(first+n)+1)*m=m*(q+first+1)+m*n by ring,pow_add]
    simp only [pow_mul]
  · ring

/-- The exact positive rho^2,rho^3,rho^4 tail used in the producer's M budget. -/
def pureFluxCovarianceMuTailBudget (q first : ℕ) : ℝ :=
  (233/100:ℝ)*
    ((((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))^2)*
        (1/3:ℝ)^(2*(q+first+1))/(1-(1/3:ℝ)^2)+
    2*((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))*(Numerics.Inverse.invCov0CA:ℝ)*
        (1/3:ℝ)^(3*(q+first+1))/(1-(1/3:ℝ)^3)+
    (Numerics.Inverse.invCov0CA:ℝ)^2*(1/3:ℝ)^(4*(q+first+1))/(1-(1/3:ℝ)^4))

/-- The complete deterministic majorant tail has exactly its source sum. -/
theorem pureFlux_covariance_mu_majorant_hasSum (q first : ℕ) :
    HasSum (fun n : ℕ => pureFluxCovarianceMuMajorant q (first+n))
      (pureFluxCovarianceMuTailBudget q first) := by
  have h2 := (pureFlux_covariance_rho_power_hasSum q first 2 (by norm_num)).mul_left
    (((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))^2)
  have h3 := (pureFlux_covariance_rho_power_hasSum q first 3 (by norm_num)).mul_left
    (2*((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))*(Numerics.Inverse.invCov0CA:ℝ))
  have h4 := (pureFlux_covariance_rho_power_hasSum q first 4 (by norm_num)).mul_left
    ((Numerics.Inverse.invCov0CA:ℝ)^2)
  convert ((h2.add h3).add h4).mul_left (233/100:ℝ) using 1
  · funext n
    rfl
  · unfold pureFluxCovarianceMuTailBudget
    ring

/-- The actual covariance/feedback coefficients are summable on every complete
source tail and obey the literal producer polynomial budget. -/
theorem pureFlux_covariance_mu_tail_summable (q first : ℕ) :
    Summable (fun n : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA q (first+n)) (pureFluxCovarianceB q (first+n))) ∧
      (∑' n : ℕ, pureFluxCovarianceMu (pureFluxCovarianceA q (first+n)) (pureFluxCovarianceB q (first+n))) ≤
        pureFluxCovarianceMuTailBudget q first := by
  have hs := pureFlux_covariance_mu_majorant_hasSum q first
  have h0 (n : ℕ) : 0 ≤ pureFluxCovarianceMu (pureFluxCovarianceA q (first+n)) (pureFluxCovarianceB q (first+n)) :=
    (pureFlux_covariance_mu_lower _ _).1
  have hb (n : ℕ) := pureFlux_covariance_mu_le_majorant q (first+n)
  have hsum := hs.summable.of_nonneg_of_le h0 hb
  exact ⟨hsum,(hsum.tsum_le_tsum hb hs.summable).trans_eq hs.tsum_eq⟩

end
end ASDExplicitGamma.Inverse
