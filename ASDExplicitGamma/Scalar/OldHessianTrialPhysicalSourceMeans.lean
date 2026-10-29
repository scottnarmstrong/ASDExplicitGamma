module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalFrame
public import ASDExplicitGamma.Scalar.LowerChainInput
public import ASDExplicitGamma.Native.OldSignedSourceHistoryStationarity

/-! The actual large-parent coarse/fine traces consume exactly the proved
completed r4/r5 source means, preserving theta and the certified rational rows. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Stationarity and the exact physical frame join identify the true
partition trace mean at every parent scale and depth. -/
theorem old_hessian_physical_trace_mean_eq (M : ABKModel 2) (n m : ℤ) (depth : ℕ) :
    let T := fun omega => descendantsAverage (originCube 2 n) depth (fun U => traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient n m omega)) 1)
    Integrable T (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ omega,T omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
        ∫ omega,cutoffTraceDefect M m (n-(depth:ℤ)) omega ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  intro T
  have he : T=fun omega => rawWeakTraceSequence M m (originCube 2 n) 0 omega depth :=
    funext (fun omega => old_hessian_old_open_trace_sequence M n m omega depth)
  rw [he]
  refine ⟨old_signed_source_trace_integrable M m (originCube 2 n) 0 (by norm_num) depth,?_⟩
  rw [old_signed_source_trace_mean_eq_depth M m (originCube 2 n) 0 (by norm_num) depth]
  apply integral_congr_ae
  filter_upwards with omega
  change traceDefect (cubeSet (originCube 2 (n-(depth:ℤ))))
    (Model.partialInsertedCoefficient M m 0 omega).toFun (Annealed.sigmaBar M m)=_
  have hz : (Model.partialInsertedCoefficient M m 0 omega).toFun=
      (Cutoff.coefficientCutoff M.nu m omega).toFun :=
    funext (fun x => old_hessian_partial_zero M m omega x)
  rw [hz]
  rfl

/-- The actual r4/r5 trace on Q_(m+129) has its exact certified completed
source cap. The large-parent spatial average introduces no extra population
factor or source estimate hypothesis. -/
theorem old_hessian_physical_source_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N)
    (r : ℕ) (hr : r=4 ∨ r=5) :
    let T := fun omega => descendantsAverage (originCube 2 (m+129)) (129+r) (fun U =>
      traceDefect (openCubeSet U) (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m omega)) 1)
    Integrable T (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ omega,T omega ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        theta M*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ) := by
  intro T
  have htrace := old_hessian_physical_trace_mean_eq M (m+129) m (129+r)
  have hscale : m+129-((129+r:ℕ):ℤ)=m-(r:ℤ) := by omega
  dsimp only at htrace
  rw [hscale] at htrace
  refine ⟨htrace.1,?_⟩
  rw [htrace.2]
  obtain ⟨_,_,h4,h5,_,_,_⟩ := scalar_lower_input_bridge M h hM hg N hpast m hm
  have hc : nativeCompletedSourceMean M m r ≤
      ENNReal.ofReal (theta M*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ)) := by
    rcases hr with hr|hr
    · subst r
      exact h4
    · subst r
      exact h5
  have hcap : 0≤theta M*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ) := by
    apply mul_nonneg (cold_theta_pos M).le
    rcases hr with hr|hr <;> subst r <;> norm_num [nativeSourceExactMeanCaps]
  rw [nativeCompletedSourceMean,←ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoffTraceDefect M m (m-(r:ℤ)))
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m (m-(r:ℤ))))] at hc
  exact (ENNReal.ofReal_le_ofReal_iff hcap).mp hc

end
end ASDExplicitGamma.Scalar
