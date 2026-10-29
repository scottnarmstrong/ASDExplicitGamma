module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseTracePopulation
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaMoments

/-! The genuine coarse source potential is paid by the actual grouped OLD
weak proxy, preserving its root-zero alpha² before any expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section

/-- The complete actual coarse shifted trace and coarse potential weak
bill are controlled by the literal grouped fine-source OLD proxy. Every
convergence and population input is proved internally. -/
theorem old_hessian_actual_coarse_theta_join
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let k := oldHessianOldOpenCoefficient (m+129) m ω
      oldHessianCoarseShiftedTrace Q 133 M.nu (Annealed.sigmaBar M m) k≤
        oldHessianGroupedOldTheta M m ω ∧
      oldHessianCoarseWeakBill Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k ≤
        inverseHistoryDiscount^2*oldHessianGroupedOldTheta M m ω := by
  filter_upwards [old_hessian_actual_coarse_trace_term_bank M h hM hg N hpast m hm,
    old_hessian_grouped_old_theta_summable M h hM hg N hpast m hm] with ω hpop hgroup
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let p := 1-inverseHistoryDiscount^2
  let E := fun j => inverseHistoryDiscount^(2*j)*oldHessianCoarseTraceTerm Q 133 M.nu
    (Annealed.sigmaBar M m) k j
  have hp0 : 0≤p := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hactual := old_hessian_coarse_shifted_trace_series Q 133 M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  have hterm (j : ℕ) : p*E j≤oldHessianGroupedOldThetaTerm M m j ω := by
    have hh := mul_le_mul_of_nonneg_left (hpop j)
      (mul_nonneg hp0 (pow_nonneg inverse_history_discount_range.1.le (2*j)))
    convert hh using 1 <;>
      (dsimp only [oldHessianGroupedOldThetaTerm,oldHessianFineDepthTrace,p,E,Q,k]
       norm_num only [inverseBankCap]
       ring)
  have hs := (hactual.1.mul_left p).tsum_le_tsum hterm hgroup
  rw [tsum_mul_left,←old_hessian_grouped_old_theta_series] at hs
  have hbound : oldHessianCoarseShiftedTrace Q 133 M.nu (Annealed.sigmaBar M m) k≤
      oldHessianGroupedOldTheta M m ω := by
    rw [hactual.2]
    exact hs
  exact ⟨hbound,(old_hessian_coarse_weak_shifted_trace Q 133 M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k).trans
      (mul_le_mul_of_nonneg_left hbound (sq_nonneg _))⟩

end
end ASDExplicitGamma.Scalar
