module

public import ASDExplicitGamma.Native.OldSignedFull64Control
public import ASDExplicitGamma.Inverse.PureFluxCovarianceRows

/-! Sharp source covariance decay on the OLD mesh-five depth sequence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Inverse Variational
noncomputable section

/-- Both source covariance rows keep the spatial decay and their distinct
constants; all radical comparisons are exact rational certificates. -/
theorem old_signed_source_covariance_AB_decay (j : ℕ) :
    pureFluxCovarianceA 0 (6+j-1) ≤ (3/200)*((1/3:ℝ)^j) ∧
    pureFluxCovarianceB 0 (6+j-1) ≤ (3/250)*((1/3:ℝ)^j) := by
  let z : ℝ := (1/3:ℝ)^j
  have hz : 0≤z := by dsimp [z]; positivity
  have hz1 : z≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hz2 : z^2≤z := by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hz1)]
  have h78 : Real.sqrt ((78/5:ℝ)/2) ≤ 14/5 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h156 : Real.sqrt (2*(78/5:ℝ)) ≤ 28/5 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h46488 : Real.sqrt (2*((3432/5:ℝ)+(78/5:ℝ)^2)) ≤ 44 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h785 : Real.sqrt (78/5:ℝ) ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h23244 : Real.sqrt ((3432/5:ℝ)+(78/5:ℝ)^2) ≤ 31 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hlinear (c d : ℝ) (hc : c≤d) : c*(z/729)≤d*(z/729) :=
    mul_le_mul_of_nonneg_right hc (div_nonneg hz (by norm_num))
  have hquad (c d : ℝ) (hc : c≤d) : c*(z/729)^2≤d*(z/729)^2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hA0 := hlinear _ _ h78
  have hA1 := hlinear _ _ h156
  have hA2 := hquad _ _ h46488
  have hB1 := hlinear _ _ h785
  have hB2 := hquad _ _ h23244
  have hp := old_signed_full64_depth_parameters 0 j
  dsimp only at hp
  simp only [pureFluxCovarianceA,pureFluxCovarianceB,pureFluxCovarianceAr,
    pureFluxCovarianceBA,pureFluxCovarianceBB,pureFluxCovarianceCA,pureFluxCovarianceCB,
    hp.2.2.1,hp.2.2.2]
  change _ ≤ (3/200)*z ∧ _ ≤ (3/250)*z
  constructor <;> nlinarith only [hA0,hA1,hA2,hB1,hB2,hz2,hz]

/-- The positive feedback root is bounded quadratically in the spatial decay. -/
theorem old_signed_source_covariance_mu_decay (j : ℕ) :
    pureFluxCovarianceMu (pureFluxCovarianceA 0 (6+j-1))
      (pureFluxCovarianceB 0 (6+j-1)) ≤ (1/2500)*((1/3:ℝ)^j)^2 := by
  let z : ℝ := (1/3:ℝ)^j
  have hz : 0≤z := by dsimp [z]; positivity
  have hrows := pureFlux_covariance_rows_order 0 (6+j-1)
  have hcaps := old_signed_source_covariance_AB_decay j
  apply (pureFlux_covariance_mu_mono _ _ ((3/200)*z) ((3/250)*z)
    (hrows.1.trans hrows.2) hrows.1 hcaps.1 hcaps.2).trans
  apply pureFlux_covariance_mu_le_of_certificate
  · nlinarith only [sq_nonneg z]
  · nlinarith only [sq_nonneg (z^2)]

/-- The source mixed row is bounded by the already certified outward row. -/
theorem old_signed_source_kappa_decay (z : ℝ) (hz : 0≤z) :
    lemmaVH2kn (z/729) (z/729) ≤ (1/10000)*z^2 :=
  (lemmaVH2kn_le_rawTraceRemainderKappaF (by positivity) (by positivity)).trans
    (old_signed_remainder_kappa_decay z)

end
end ASDExplicitGamma.Native
