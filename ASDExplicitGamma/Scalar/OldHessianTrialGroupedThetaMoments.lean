module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTermMoment
public import ASDExplicitGamma.Scalar.OldHessianTrialPositiveSeries

/-! Complete grouped OLD weak-proxy moments on the actual scalar parent.
All source means, full depth tails and correlated bank payments are proved
before the proxy is consumed by the mixed trial's source-square estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The exact scalar-parent counterpart of the weighted OLD mixed bridge:
all global powers0..3, actual fine traces and grouped local depth banks,
with AE convergence and real integrability as conclusions. -/
theorem old_hessian_grouped_old_theta_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (k : ℕ) (hk : k≤3) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j => oldHessianGroupedBank M m ω^k*oldHessianGroupedOldThetaTerm M m j ω)) ∧
    Integrable (fun ω => oldHessianGroupedBank M m ω^k*oldHessianGroupedOldTheta M m ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω^k*oldHessianGroupedOldTheta M m ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (14103/10000:ℝ)^k*(mixedXiPreCap M+(1/10^12:ℝ)*theta M) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun (j : ℕ) ω => oldHessianGroupedBank M m ω^k*oldHessianGroupedOldThetaTerm M m j ω
  let S := fun j : ℕ => mixedBridgeLocalWeight M j*inSourceMeanActual M m (5+j) 0
  let C := fun j : ℕ => (14103/10000:ℝ)^k*S j+oldHessianWeakRareBudget M k j
  have hsource := mixed_bridge_local_mean_transport M h hM hg N hpast m hm 0 (by norm_num)
  simp only [zero_mul,add_zero] at hsource
  have hrare := old_hessian_weak_rare_budget M hg k hk
  have hsourceS : Summable S := hsource.1
  have hC : Summable C := (hsourceS.mul_left ((14103/10000:ℝ)^k)).add hrare.1
  have hf (j : ℕ) : Integrable (f j) μ :=
    (old_hessian_grouped_theta_term_moment M h hM hg N hpast m hm k hk j).1
  have hn (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0≤f j ω :=
    mul_nonneg (pow_nonneg ENNReal.toReal_nonneg k) (old_hessian_grouped_old_theta_term_nonneg M m j ω)
  have hb (j : ℕ) : (∫ ω,f j ω ∂μ)≤C j := by
    have hh := (old_hessian_grouped_theta_term_moment M h hM hg N hpast m hm k hk j).2
    exact hh.trans_eq (by dsimp [C,S]; ring)
  have hs := old_hessian_positive_series_integral μ f C hf hn hC hb
  have he : (fun ω => oldHessianGroupedBank M m ω^k*oldHessianGroupedOldTheta M m ω)=
      (fun ω => ∑' j,f j ω) := by
    funext ω
    rw [old_hessian_grouped_old_theta_series]
    exact (tsum_mul_left).symm
  refine ⟨hs.1,he.symm ▸ hs.2.1,?_⟩
  rw [he]
  have hsum : (∑' j,C j)=(14103/10000:ℝ)^k*(∑' j,S j)+(∑' j,oldHessianWeakRareBudget M k j) := by
    rw [Summable.tsum_add (hsourceS.mul_left ((14103/10000:ℝ)^k)) hrare.1,tsum_mul_left]
  have hβ : 1≤(14103/10000:ℝ)^k := one_le_pow₀ (by norm_num)
  have hθ : 0≤(1/10^12:ℝ)*theta M := mul_nonneg (by norm_num) (cold_theta_pos M).le
  calc
    _ ≤ ∑' j,C j := hs.2.2
    _ = (14103/10000:ℝ)^k*(∑' j,S j)+(∑' j,oldHessianWeakRareBudget M k j) := hsum
    _ ≤ (14103/10000:ℝ)^k*mixedXiPreCap M+(1/10^12:ℝ)*theta M :=
      add_le_add (mul_le_mul_of_nonneg_left hsource.2 (pow_nonneg (by norm_num) k)) hrare.2
    _ ≤ (14103/10000:ℝ)^k*mixedXiPreCap M+(14103/10000:ℝ)^k*((1/10^12:ℝ)*theta M) :=
      add_le_add le_rfl (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hβ hθ)
    _ = _ := (mul_add _ _ _).symm

/-- Actual grouped OLD weak series converge a.e. before any real proxy is
used in a pointwise trial bound. -/
theorem old_hessian_grouped_old_theta_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j => oldHessianGroupedOldThetaTerm M m j ω) := by
  simpa only [pow_zero,one_mul] using
    (old_hessian_grouped_old_theta_moments M h hM hg N hpast m hm 0 (by norm_num)).1

end
end ASDExplicitGamma.Scalar
