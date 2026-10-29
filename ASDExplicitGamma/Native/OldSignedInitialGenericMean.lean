module

public import ASDExplicitGamma.Native.GenericSourceBandEndpoint
public import ASDExplicitGamma.Native.GenericSourceDepthRows

/-! Initial OLD means from the generic producer anchored at each cell scale. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Cold Inverse Variational Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- For the q1 initial law, every strictly smaller cell scale is already an
available native cutoff. Apply the generic band producer there directly;
this avoids paying an additional spatial subdivision in a first-moment bound. -/
theorem old_signed_initial_generic_depth_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l < n,nativeInductionState M h l)
    (r : ℕ) (hr : 1≤r) (hr160 : r≤160) :
    (∫ ω,cutoffTraceDefect M n (n-(r:ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*nativeSourceGenericMeanProfile (17/50000) 1 r := by
  let q : ℤ := n-(r:ℤ)
  have hqn : q<n := by dsimp [q]; omega
  have hstates : ∀ l<q,nativeInductionState M h l := fun l hl => hpast l (hl.trans hqn)
  have hh := native_source_completed_generic_mean M h hM hg q hstates (hpast q hqn)
    r hr (by omega)
  have hqn' : q+(r:ℤ)=n := by dsimp [q]; omega
  rw [hqn'] at hh
  have hprofile : (∫ ω,cutoffTraceDefect M n (n-(r:ℤ)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ nativeSourceGenericMeanProfile M.gamma (theta M) r := by
    simpa only [nativeSourceGenericMeanProfile,ite_eq_left hr160,q] using hh
  exact hprofile.trans (native_source_generic_mean_profile_degree M.gamma (theta M) r
    M.shellPrefix.gamma_pos.le hg rfl (by omega))

end
end ASDExplicitGamma.Native
