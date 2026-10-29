module

public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Inverse.RawMomentRoot
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Cold.TwentiethMomentNorm
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Model.Translation

/-! A fixed-time p=20 trace-root increment helper for MA-ENVELOPE-H. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Inverse
open scoped Topology ENNReal

/-- The fixed-time twentieth-root trace increment follows from the exact
p=20 generator premise used by raw-trace shell transport. -/
theorem main_raw_trace_p20_root_increment_to_time_of_generator
    (q : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (U : ℝ → ℝ)
    (hU0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ U t)
    (hUInt : IntegrableOn U (Icc (0 : ℝ) 1))
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hGenerator : ∀ t ∈ Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage q M m 20) t ≤
        20 * modelTracePowerHeatAverage q M m 20 t ^ ((19 : ℝ) / 20) * U t) :
    modelTracePowerHeatAverage q M m 20 τ ^ ((20 : ℝ)⁻¹) -
      modelTracePowerHeatAverage q M m 20 0 ^ ((20 : ℝ)⁻¹) ≤
        ∫ t in (0 : ℝ)..τ, U t := by
  let σ : ℝ := (Annealed.sigmaBar M m : ℝ)
  let Φ := modelTraceObservable q M.nu σ
  let f : ℝ → ℝ := modelTracePowerHeatAverage q M m 20
  have hσ : 0 < σ := (Annealed.sigmaBar M m).2
  have hheat := exists_modelTrace_heat_and_moment_identities q M h hM m
  obtain ⟨T, v, hA, hlaw, hΦ, htraceCont, htraceHeatCont,
      htraceDeriv, htraceDeriv0, hpower⟩ := hheat
  have hmoment := hpower 20 (by norm_num : (2 : ℝ) ≤ 20)
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) := by
    apply hmoment.1.mono
    intro t ht
    exact ht.1
  have hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t := by
    intro t ht
    rw [show f t = modelTracePowerHeatAverage q M m 20 t by rfl,
      modelTracePowerHeatAverage_eq]
    unfold modelHeatAverage
    apply integral_nonneg
    intro ω
    exact Real.rpow_nonneg
      (modelTraceObservable_nonneg q M.nu σ M.nu_pos hσ
        (modelInsertedScalar (closure (cubeSet (originCube 2 q))) m t ω)) _
  have hdf : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt f (deriv f t) t := by
    intro t ht
    have hd := hmoment.2.2.1 t ht.1
    have hdfEq : deriv f t =
        modelHeatAverage (closure (cubeSet (originCube 2 q))) M m
          (modelPowerHeatGenerator Φ (fun j => T (v j)) 20) t := by
      exact hd.deriv
    rw [hdfEq]
    simpa only [f, Φ, σ] using hd
  exact raw_p20_moment_root_sub_le_integral
    hf hf0 hdf hU0 hUInt
    (by
      intro t ht
      simpa only [f] using hGenerator t ht)
    (s := 0) (t := τ)
    (by norm_num) hτ0 hτ1

/-- The model heat root estimate is the same estimate for the actual raw
four-load trace moment at the origin cell. The generator row remains the exact
input supplied by raw-trace shell transport. -/
theorem main_rawDepth_p20_trace_moment_increment_to_time_of_generator
    (q : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (U : ℝ → ℝ)
    (hU0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ U t)
    (hUInt : IntegrableOn U (Icc (0 : ℝ) 1))
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hGenerator : ∀ t ∈ Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage q M m 20) t ≤
        20 * modelTracePowerHeatAverage q M m 20 t ^ ((19 : ℝ) / 20) * U t) :
    (∫ ω, rawDepthFourLoadTrace M m q τ ω ^ 20
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((20 : ℝ)⁻¹) -
      (∫ ω, rawDepthFourLoadTrace M m q 0 ω ^ 20
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((20 : ℝ)⁻¹) ≤
        ∫ t in (0 : ℝ)..τ, U t := by
  have hmoment (s : ℝ) : modelTracePowerHeatAverage q M m 20 s =
      ∫ ω, rawDepthFourLoadTrace M m q s ω ^ 20
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    unfold modelTracePowerHeatAverage rawDepthFourLoadTrace rawCubeFourLoadTrace
    congr 1
    funext ω
    exact Real.rpow_natCast _ 20
  rw [← hmoment τ, ← hmoment 0]
  exact main_raw_trace_p20_root_increment_to_time_of_generator
    q M h hM m U hU0 hUInt τ hτ0 hτ1 hGenerator

/-- Convert the actual origin-trace twentieth moment to the L20 norm used by
the weak-history averaging step. -/
theorem main_rawDepth_lpNorm_twenty_eq_integral_root
    (M : ABKModel 2) (m q : ℤ) (t : ℝ)
    (hT : MemLp (rawDepthFourLoadTrace M m q t) 20
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    lpNorm (rawDepthFourLoadTrace M m q t) 20
        (Cutoff.cutoffSampleLaw M).toMeasure =
      (∫ ω, rawDepthFourLoadTrace M m q t ω ^ 20
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((20 : ℝ)⁻¹) := by
  have hroot :
      ((lpNorm (rawDepthFourLoadTrace M m q t) 20
        (Cutoff.cutoffSampleLaw M).toMeasure) ^ (20 : ℕ)) ^ ((20 : ℝ)⁻¹) =
      lpNorm (rawDepthFourLoadTrace M m q t) 20
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [← Real.rpow_natCast_mul
      (lpNorm_nonneg (f := rawDepthFourLoadTrace M m q t) (p := 20)
        (μ := (Cutoff.cutoffSampleLaw M).toMeasure) ) 20 ((20 : ℝ)⁻¹)]
    norm_num
  calc
    lpNorm (rawDepthFourLoadTrace M m q t) 20
        (Cutoff.cutoffSampleLaw M).toMeasure =
      ((lpNorm (rawDepthFourLoadTrace M m q t) 20
        (Cutoff.cutoffSampleLaw M).toMeasure) ^ (20 : ℕ)) ^ ((20 : ℝ)⁻¹) :=
          hroot.symm
    _ = (∫ ω, rawDepthFourLoadTrace M m q t ω ^ 20
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((20 : ℝ)⁻¹) := by
          rw [← ASDExplicitGamma.Cold.cold_lpNorm_twenty_pow hT]

/-- Partial insertion commutes with the actual real translation of the full
cutoff sample, including the deterministically scaled fresh shell. -/
theorem main_partialInsertedCoefficient_translate
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (z : Homogenization.Vec 2)
    (ω : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M m t (Cutoff.translateCutoffSample z ω) =
      translateReg z (Model.partialInsertedCoefficient M m t ω) := by
  apply RegCoeffField.ext
  intro x
  ext i j
  simp [Model.partialInsertedCoefficient, translateReg,
    Cutoff.coefficientCutoff_translateCutoffSample, Cutoff.translateCutoffSample_val,
    ShellField.translateSequence_apply, ShellField.forgetShell_translate]

/-- A trace on a translated triadic cell is the origin trace evaluated at the
translated cutoff sample. -/
theorem main_rawCubeFourLoadTrace_translate_to_origin
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rawCubeFourLoadTrace M m Q t ω =
      rawDepthFourLoadTrace M m Q.scale t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
  let z := triadicCubeShift Q
  have hQ : cubeSet Q = translateSet z (cubeSet (originCube 2 Q.scale)) := by
    simpa only [z] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hcoeff := main_partialInsertedCoefficient_translate M m t z ω
  have hfun : (Model.partialInsertedCoefficient M m t
      (Cutoff.translateCutoffSample z ω)).toFun =
      translateCoeffField z (Model.partialInsertedCoefficient M m t ω).toFun := by
    rw [hcoeff]
    rfl
  change traceDefect (cubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun
      (Annealed.sigmaBar M m : ℝ) =
    traceDefect (cubeSet (originCube 2 Q.scale))
      (Model.partialInsertedCoefficient M m t
        (Cutoff.translateCutoffSample z ω)).toFun
      (Annealed.sigmaBar M m : ℝ)
  rw [hQ, Model.traceDefect_translate, hfun]

/-- Translation of a descendant cell preserves every finite Lp norm of its
actual raw trace, whenever the origin trace belongs to that Lp space. -/
theorem main_rawCubeFourLoadTrace_lpNorm_eq_origin
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (p : ℝ≥0∞)
    (hT : MemLp (rawDepthFourLoadTrace M m Q.scale t) p
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    lpNorm (rawCubeFourLoadTrace M m Q t) p
        (Cutoff.cutoffSampleLaw M).toMeasure =
      lpNorm (rawDepthFourLoadTrace M m Q.scale t) p
        (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let z := triadicCubeShift Q
  let shift : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 :=
    fun ω => Cutoff.translateCutoffSample z ω
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample z,
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩
  have hcomp := eLpNorm_comp_measurePreserving
    (p := p) (g := rawDepthFourLoadTrace M m Q.scale t)
    hT.aestronglyMeasurable hmp
  have hfun : rawCubeFourLoadTrace M m Q t =
      fun ω => rawDepthFourLoadTrace M m Q.scale t (shift ω) := by
    funext ω
    exact main_rawCubeFourLoadTrace_translate_to_origin M m Q t ω
  rw [hfun]
  change (eLpNorm (fun ω => rawDepthFourLoadTrace M m Q.scale t (shift ω)) p μ).toReal =
    (eLpNorm (rawDepthFourLoadTrace M m Q.scale t) p μ).toReal
  exact congrArg ENNReal.toReal hcomp

/-- Lp integrability of an origin trace transfers to every translated cell. -/
theorem main_rawCubeFourLoadTrace_memLp_of_origin
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (p : ℝ≥0∞)
    (hT : MemLp (rawDepthFourLoadTrace M m Q.scale t) p
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    MemLp (rawCubeFourLoadTrace M m Q t) p
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let z := triadicCubeShift Q
  let shift : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 :=
    fun ω => Cutoff.translateCutoffSample z ω
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample z,
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩
  have hcomp : MemLp (fun ω => rawDepthFourLoadTrace M m Q.scale t (shift ω)) p μ :=
    hT.comp_measurePreserving hmp
  have hfun : rawCubeFourLoadTrace M m Q t =
      fun ω => rawDepthFourLoadTrace M m Q.scale t (shift ω) := by
    funext ω
    exact main_rawCubeFourLoadTrace_translate_to_origin M m Q t ω
  rw [hfun]
  exact hcomp

/-- A source old-profile cap propagates to every translated cell under the
exact p=20 generator premise. The remaining hypotheses are the actual L20
finiteness facts at the two endpoint times. -/
theorem main_rawCube_lpNorm_twenty_bound_of_generator
    (Q : TriadicCube 2) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (U : ℝ → ℝ)
    (hU0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ U t)
    (hUInt : IntegrableOn U (Icc (0 : ℝ) 1))
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hGenerator : ∀ t ∈ Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage Q.scale M m 20) t ≤
        20 * modelTracePowerHeatAverage Q.scale M m 20 t ^ ((19 : ℝ) / 20) * U t)
    (hT0 : MemLp (rawDepthFourLoadTrace M m Q.scale 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hTτ : MemLp (rawDepthFourLoadTrace M m Q.scale τ) 20
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (B : ℝ)
    (hB : lpNorm (rawDepthFourLoadTrace M m Q.scale 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ B) :
    lpNorm (rawCubeFourLoadTrace M m Q τ) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      B + ∫ t in (0 : ℝ)..τ, U t := by
  have hroot := main_rawDepth_p20_trace_moment_increment_to_time_of_generator
    Q.scale M h hM m U hU0 hUInt τ hτ0 hτ1 hGenerator
  have hBroot := hB
  rw [main_rawDepth_lpNorm_twenty_eq_integral_root M m Q.scale 0 hT0] at hBroot
  calc
    lpNorm (rawCubeFourLoadTrace M m Q τ) 20
        (Cutoff.cutoffSampleLaw M).toMeasure =
      lpNorm (rawDepthFourLoadTrace M m Q.scale τ) 20
        (Cutoff.cutoffSampleLaw M).toMeasure :=
          main_rawCubeFourLoadTrace_lpNorm_eq_origin M m Q τ 20 hTτ
    _ = (∫ ω, rawDepthFourLoadTrace M m Q.scale τ ω ^ 20
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ ((20 : ℝ)⁻¹) :=
          main_rawDepth_lpNorm_twenty_eq_integral_root M m Q.scale τ hTτ
    _ ≤ B + ∫ t in (0 : ℝ)..τ, U t := by linarith

end ASDExplicitGamma.Main

end
