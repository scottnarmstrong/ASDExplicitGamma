module

public import ASDExplicitGamma.Native.OldSignedInitialWeightedMean
public import ASDExplicitGamma.Native.OldSignedWeightedMeanSlopeSum

/-! Exact initial and partial mean carriers for the OLD panel inputs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Zero insertion uses the actual completed mean in precisely the same frame. -/
theorem old_signed_mean_zero_eq_integral (M : ABKModel 2) (n : ℤ) (r : ℕ) :
    inSourceMeanActual M n r 0 =
      ∫ ω,cutoffTraceDefect M n (n-(r:ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [in_source_mean_old_endpoint]
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M n (n-(r:ℤ))))
    (integrable_cutoffTraceDefect M n (n-(r:ℤ))).aestronglyMeasurable

/-- The physical partial mean is nonnegative at every admissible heat time. -/
theorem old_signed_partial_mean_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t : ℝ) : 0 ≤ inSourceMeanActual M n r t :=
  integral_nonneg (raw_depth_four_load_trace_nonneg M n (n-(r:ℤ)) t)

/-- The actual depth-five mean is paid by a coarse affine envelope that fits
strictly inside the fixed source panel; no q1 or refined row is assumed. -/
theorem old_signed_actual_mean_affine
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    inSourceMeanActual M n 5 t ≤ theta M*((7/50:ℝ)+(1/50)*t) := by
  have hinit := old_signed_initial_mean_prefix_pointwise M h hM hg n
    (fun l hl => hpast l hl.le) 0 (by norm_num)
  have hstart : inSourceMeanActual M n 5 0≤theta M*(7/50) := by
    rw [old_signed_mean_zero_eq_integral]
    simpa only [Nat.add_zero,Nat.cast_zero,mul_zero,add_zero] using hinit
  have htransport := old_signed_actual_mean_source_transport M h hM hg n
    (fun l hl => hpast l hl.le) 5 t ht
  have hslope := mul_le_mul_of_nonneg_left
    (old_signed_mean_source_five_cap M h n hg (hpast n le_rfl)) ht.1
  have hh := htransport.trans (add_le_add hstart hslope)
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
