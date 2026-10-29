module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks

/-! Exact refined geometry for the actual finite drift coefficient sums. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Variational Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- The completed OLD label n and child scale n-1 give precisely the
refined source's offset d+2, not the unrefined offset d+1. -/
theorem heatVHEATDrift_source_kappa_geometry_eq (n : ℤ) (d : Fin 9) :
    heatVHEATDriftKappa n d=
      lemmaVH2kn (pureFluxCovarianceRho 0 (d.val+1)) (pureFluxCovarianceDelta 0 (d.val+1)) := by
  have hlabel : n+((d.val+1:ℕ):ℤ)=(n-1)+((d.val+2:ℕ):ℤ) := by omega
  dsimp only [heatVHEATDriftKappa]
  rw [hlabel,pureFlux_bank_source_rho (n-1) (d.val+2) (by omega),
    pureFlux_bank_source_delta (n-1) (d.val+2) (by omega)]
  congr 2

/-- Actual refined mixed and remainder coefficients are nonnegative. -/
theorem heatVHEATDrift_source_coefficients_nonneg (n : ℤ) (d : Fin 9) :
    0 ≤ heatVHEATDriftKappa n d ∧ 0 ≤ heatVHEATDriftMu d := by
  constructor
  · rw [heatVHEATDrift_source_kappa_geometry_eq]
    have hr := (pureFlux_covariance_rho_pos 0 (d.val+1)).le
    have hd := (pureFlux_covariance_delta_bounds 0 (d.val+1)).1
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  · exact (pureFlux_covariance_mu_lower _ _).1

/-- The actual finite sums retain positivity before any numeric certificate
is consumed. Their definitions keep all nine positive shells. -/
theorem heatVHEATDrift_source_sums_nonneg (n : ℤ) :
    0 ≤ heatVHEATDriftKActual n ∧ 0 ≤ heatVHEATDriftCActual := by
  exact ⟨Finset.sum_nonneg (fun d _ => (heatVHEATDrift_source_coefficients_nonneg n d).1),
    Finset.sum_nonneg (fun d _ => (heatVHEATDrift_source_coefficients_nonneg n d).2)⟩

/-- Exact reindexing to the owner's refined coefficient row q=1. -/
theorem heatVHEATDrift_source_coefficients_eq_refined_row (n : ℤ) (d : Fin 9) :
    heatVHEATDriftKappa n d=
      lemmaVH2kn (pureFluxCovarianceRho 1 d.val) (pureFluxCovarianceDelta 1 d.val) ∧
    heatVHEATDriftMu d=
      pureFluxCovarianceMu (pureFluxCovarianceA 1 d.val) (pureFluxCovarianceB 1 d.val) := by
  have hr : pureFluxCovarianceRho 0 (d.val+1)=pureFluxCovarianceRho 1 d.val := by
    unfold pureFluxCovarianceRho
    congr 1
    omega
  have hd : pureFluxCovarianceDelta 0 (d.val+1)=pureFluxCovarianceDelta 1 d.val := by
    unfold pureFluxCovarianceDelta
    rw [hr]
  constructor
  · rw [heatVHEATDrift_source_kappa_geometry_eq,hr,hd]
  · simp only [heatVHEATDriftMu,pureFluxCovarianceA,pureFluxCovarianceB,hr,hd]

/-- The complete actual sums are exactly the refined q=1 row. This is the
identification needed to consume the owner's finite coefficient certificate. -/
theorem heatVHEATDrift_source_sums_eq_refined_row (n : ℤ) :
    heatVHEATDriftKActual n=
      ∑ d : Fin 9,lemmaVH2kn (pureFluxCovarianceRho 1 d.val) (pureFluxCovarianceDelta 1 d.val) ∧
    heatVHEATDriftCActual=
      ∑ d : Fin 9,pureFluxCovarianceMu (pureFluxCovarianceA 1 d.val) (pureFluxCovarianceB 1 d.val) := by
  constructor
  · exact Finset.sum_congr rfl (fun d _ => (heatVHEATDrift_source_coefficients_eq_refined_row n d).1)
  · exact Finset.sum_congr rfl (fun d _ => (heatVHEATDrift_source_coefficients_eq_refined_row n d).2)

end
end ASDExplicitGamma.Native
