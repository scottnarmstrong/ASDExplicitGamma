module

public import ASDExplicitGamma.Native.GenericSourceEndpoints
public import ASDExplicitGamma.Native.GenericSourcePass

/-! The actual initial native root and the unrefined generic source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- At a completed starting label the compact observable is the frozen
native trace defect, in the exact true frame. -/
theorem native_source_model_trace_older_eq (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable n M.nu (Annealed.sigmaBar M n)
      (olderField (closure (cubeSet (originCube 2 n))) n ω) =
      cutoffTraceDefect M n n ω := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have he : Model.partialInsertedCoefficient M n 0 ω = Cutoff.coefficientCutoff M.nu n ω := by
    ext x i j
    simp [Model.partialInsertedCoefficient,RegCoeffField.add_apply,RegCoeffField.smul_apply]
  have hh := modelTraceObservable_inserted_eq_traceDefect n M ell n hK
    (Annealed.sigmaBar M n) 0 ω
  rw [(native_source_inserted_endpoints K ell n hK ω).1,he] at hh
  exact hh

/-- The initial band root is the real norm of the frozen root20 coordinate;
finiteness is supplied by the native state before taking toReal. -/
theorem native_source_band_initial_root_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hstate : nativeInductionState M h n) :
    nativeSourceBandRoot M n 0 ≤ (2013/10000:ℝ)*theta M := by
  have hcap := hstate.2.2.1
  have hmem : MemLp (cutoffTraceDefect M n n) (ENNReal.ofReal 20)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply memLp_iff.mpr
    have hh : root20 M n < ⊤ := hcap.trans_lt ENNReal.ofReal_lt_top
    simpa only [root20,show ENNReal.ofReal (20:ℝ)=(20:ℝ≥0∞) by norm_num] using hh
  have heq : nativeSourceBandRoot M n 0 =
      (root20 M n).toReal := by
    unfold nativeSourceBandRoot
    simp only [Nat.cast_zero,add_zero]
    simp_rw [native_source_model_trace_older_eq]
    have hh := positiveLpNorm_eq_eLpNorm_toReal (Cutoff.cutoffSampleLaw M).toMeasure
      (p := 20) (by norm_num) (cutoffTraceDefect M n n) (cutoffTraceDefect_nonneg M n n) hmem
    simpa only [positiveLpNorm,root20,
      show ENNReal.ofReal (20:ℝ)=(20:ℝ≥0∞) by norm_num] using hh
  rw [heq]
  have ht : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (by norm_num) ht))

end
end ASDExplicitGamma.Native
