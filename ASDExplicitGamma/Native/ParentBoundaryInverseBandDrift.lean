module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBandGenerator

/-! Average the actual band inverse lower generator using the genuine
global-bank cubic moment, retaining its correlated positive reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
open scoped ENNReal
noncomputable section

/-- Actual inverse trace and its history-weighted cubic are integrable
under the fixed-frame simultaneous-band law. -/
theorem parent_boundary_inverse_band_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t≤1) :
    let d := fun omega : Cutoff.CutoffSample 2 => mainInverseObservable n M.nu
      (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t omega)
    Integrable d (Cutoff.cutoffSampleLaw M).toMeasure ∧
      Integrable (fun omega => (nativeSourceBandHistory M n height t omega).toReal^2*d omega)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
  intro d
  have hb := parent_boundary_inverse_band_global_bank M h hM hg n height hpast t ht
  have hcap : 0≤(inverseBankCap .globalInverse:ℝ) := by norm_num [inverseBankCap]
  have hmem := main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    (nativeSourceBandHistory M n height t) (inverseBankCap .globalInverse:ℝ) hcap
    hb.history_finite hb.total_L128
  exact main_inverse_deficit_trace_integrability_of_lp128 _ d
    (parent_boundary_inverse_band_observable_measurable M n height t)
    hmem.1 (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    (parent_boundary_inverse_band_history_bounds M h hM hg n height hpast t ht)

/-- The actual expected inverse generator satisfies the precise affine
lower drift consumed by the interior-time signed flow comparison. -/
theorem parent_boundary_inverse_band_drift
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t≤1) :
    -mainKappa (parentBoundaryBandInverseClock M h n height)*
        parentBoundaryBandInverseMean M n height t-
      mainKappa (parentBoundaryBandInverseClock M h n height)*mainRho≤
        ∫ omega,parentBoundaryBandInverseGenerator M h n height t omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let mu := parentBoundaryBandInverseClock M h n height
  let d := fun omega : Cutoff.CutoffSample 2 => mainInverseObservable n M.nu
    (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t omega)
  let v := fun omega : Cutoff.CutoffSample 2 => (nativeSourceBandHistory M n height t omega).toReal^2*d omega
  let law := (Cutoff.cutoffSampleLaw M).toMeasure
  have hmu : 0≤mu := parent_boundary_inverse_band_clock_nonneg M h n height
  have hint := parent_boundary_inverse_band_integrable M h hM hg n height hpast t ht
  have hgen := parent_boundary_inverse_band_generator_integrable M h hM n height hheight t
  have hleft : Integrable (fun omega => -(mu*(nativeSourceBandHistory M n height t omega).toReal^2*d omega)) law := by
    convert hint.2.const_mul (-mu) using 1
    funext omega
    dsimp [v,d]
    ring
  have hmoment := parent_boundary_inverse_band_cubic_moment M h hM hg n height hpast t ht
  have hdelta : (inverseBankCap .globalInverse:ℝ)^2*mainRho=
      2*(2*(inverseBankCap .globalInverse:ℝ)^2*(inverseBankReserve .globalInverse:ℝ)+
        3*(inverseBankCap .globalInverse:ℝ)*(inverseBankReserve .globalInverse:ℝ)^2+
        (inverseBankReserve .globalInverse:ℝ)^3) := by
    norm_num [mainRho,mainBeta,mainEpsNew,inverseBankCap,inverseBankReserve]
  have hcap : (inverseBankCap .globalInverse:ℝ)=mainBeta := by norm_num [inverseBankCap,mainBeta]
  have hpoint := parent_boundary_inverse_band_generator_lower M h hM hg n height hpast t ht
  calc
    _ = -mu*((inverseBankCap .globalInverse:ℝ)^2*parentBoundaryBandInverseMean M n height t+
        2*(2*(inverseBankCap .globalInverse:ℝ)^2*(inverseBankReserve .globalInverse:ℝ)+
          3*(inverseBankCap .globalInverse:ℝ)*(inverseBankReserve .globalInverse:ℝ)^2+
          (inverseBankReserve .globalInverse:ℝ)^3)) := by
      rw [←hdelta,hcap]
      dsimp only [mainKappa,mu]
      ring
    _ ≤ -mu*(∫ omega,v omega ∂law) := by
      convert neg_le_neg (mul_le_mul_of_nonneg_left hmoment hmu) using 1 <;> ring
    _ = ∫ omega,-(mu*(nativeSourceBandHistory M n height t omega).toReal^2*d omega) ∂law := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with omega
      dsimp [v]
      ring
    _ ≤ _ := integral_mono_ae hleft hgen hpoint

end
end ASDExplicitGamma.Native
