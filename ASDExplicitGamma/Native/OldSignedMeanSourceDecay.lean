module

public import ASDExplicitGamma.Native.OldSignedMeanSourceTransport
public import ASDExplicitGamma.Native.OldSignedSourceCovarianceDecay

/-! Retained depth decay in the sharp OLD first-moment source coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Inverse Variational Algsuperdiff.Section3
noncomputable section

/-- The literal inverse factors fit a rational mixed/remainder coefficient. -/
theorem old_signed_mean_source_brace (z C F k u : ℝ)
    (hC : 1≤C) (hF : 0≤F)
    (hk : k≤(1/10000)*z^2) (hu : u≤(1/2500)*z^2) :
    C*(2*(3683/2500:ℝ)+2*k*(3683/2500)*F+C*u*(3683/2500)^2*F) ≤
      3*C+(3/2500)*z^2*C^2*F := by
  have hC0 : 0≤C := (by norm_num : (0:ℝ)≤1).trans hC
  have hk' := mul_le_mul_of_nonneg_right hk
    (by positivity : (0:ℝ)≤2*(3683/2500)*F)
  have hu' := mul_le_mul_of_nonneg_right hu
    (by positivity : (0:ℝ)≤C*(3683/2500)^2*F)
  have hzF : z^2*F ≤ z^2*C*F := by
    have hh := mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg z) hF)
    nlinarith only [hh]
  have hinside : 2*(3683/2500:ℝ)+2*k*(3683/2500)*F+C*u*(3683/2500)^2*F ≤
      3+(3/2500)*z^2*C*F := by
    nlinarith only [hk',hu',hzF,mul_nonneg (mul_nonneg (sq_nonneg z) hC0) hF]
  have hh := mul_le_mul_of_nonneg_left hinside hC0
  nlinarith only [hh]

/-- Actual covariance coefficients and frame clocks reduce to two geometric
profiles, before summing any spatial history. -/
theorem old_signed_mean_source_cap_decay (M : ABKModel 2) (h : ℝ) (n : ℤ) (j : ℕ) :
    oldSignedMeanSourceCap M h n (5+j) ≤
      ((q3ModelAmplitude M h (n+1))^2/(Annealed.sigmaBar M n:ℝ)^2)*
        (3*rawTraceOldFrameP20LocalClock M.gamma (6+j)+
          (3/2500)*((1/3:ℝ)^j)^2*rawTraceOldFrameP20LocalClock M.gamma (6+j)^2*
            oldSignedP20Full64Cap M.gamma (6+j)) := by
  let q : ℤ := n-((5+j:ℕ):ℤ)
  have hJ : q+((6+j:ℕ):ℤ)=n+1 := by dsimp [q]; omega
  have hp := old_signed_full64_depth_parameters q j
  dsimp only at hp
  have hz : 0≤(1/3:ℝ)^j := pow_nonneg (by norm_num) j
  have hg := M.shellPrefix.gamma_pos.le
  have hC : 1≤rawTraceOldFrameP20LocalClock M.gamma (6+j) := by
    unfold rawTraceOldFrameP20LocalClock
    apply Real.one_le_rpow (by norm_num)
    have hs : (1:ℝ)≤((6+j:ℕ):ℝ) := by exact_mod_cast (show 1≤6+j by omega)
    positivity
  have hF : 0≤oldSignedP20Full64Cap M.gamma (6+j) := by
    unfold oldSignedP20Full64Cap
    positivity
  have hbrace := old_signed_mean_source_brace ((1/3:ℝ)^j)
    (rawTraceOldFrameP20LocalClock M.gamma (6+j)) (oldSignedP20Full64Cap M.gamma (6+j))
    (lemmaVH2kn (((1/3:ℝ)^j)/729) (((1/3:ℝ)^j)/729))
    (pureFluxCovarianceMu (pureFluxCovarianceA 0 (6+j-1)) (pureFluxCovarianceB 0 (6+j-1)))
    hC hF (old_signed_source_kappa_decay _ hz) (old_signed_source_covariance_mu_decay j)
  dsimp only [oldSignedMeanSourceCap]
  rw [show 5+j+1=6+j by omega]
  rw [mul_assoc]
  change ((q3ModelAmplitude M h (q+((6+j:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2)*_≤_
  rw [hp.1,hp.2.1,hJ]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbrace
    (div_nonneg (sq_nonneg (q3ModelAmplitude M h (n+1)))
      (sq_nonneg (Annealed.sigmaBar M n:ℝ)))

end
end ASDExplicitGamma.Native
