module

public import ASDExplicitGamma.Cold.NativeStrongHistory
public import Mathlib.Probability.IdentDistrib

/-! # Genuine translated-cell trace laws at one fixed completed coefficient -/

@[expose] public section
noncomputable section
open MeasureTheory Algsuperdiff.Section3 Homogenization
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual cell trace in the true frame of the fixed old label m. -/
def coldNativeCellTrace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) : Cutoff.CutoffSample 2 → ℝ :=
  fun ω => traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m:ℝ)

/-- Actual cell traces are measurable without choosing random harmonic solutions. -/
theorem coldNativeCellTrace_measurable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    Measurable (coldNativeCellTrace M m Q) := by
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu m
  have hX : Measurable X := Cutoff.measurable_coefficientCutoff M.nu m
  have hell : ∀ ω, Homogenization.Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m
  have hUL := Provider.BadEvents.measurable_comp_coarseB_cubeSet hX hell Q
  have hLR := Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet hX hell Q
  have htraceUL : Measurable (fun ω => Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft) := by
    unfold Matrix.trace
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
  have htraceLR : Measurable (fun ω => Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight) := by
    unfold Matrix.trace
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
  exact ((htraceUL.const_mul (Annealed.sigmaBar M m:ℝ)⁻¹).add
    (htraceLR.const_mul (Annealed.sigmaBar M m:ℝ))).sub_const 4

/-- Every actual cell trace is nonnegative. -/
theorem coldNativeCellTrace_nonneg (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ coldNativeCellTrace M m Q ω := by
  obtain ⟨Λ,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
  exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
    (Annealed.sigmaBar_characterization M m).1

/-- The actual cell trace distribution is exactly the observable of the genuine coefficient law. -/
theorem coldNativeCellTrace_map (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    Measure.map (coldNativeCellTrace M m Q) (Cutoff.cutoffSampleLaw M).toMeasure =
      Measure.map (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun (Annealed.sigmaBar M m:ℝ))
        (Cutoff.coefficientCutoffLaw M m) := by
  have hm := Model.aemeasurable_traceDefect_cutoffLaw M m Q (Annealed.sigmaBar M m:ℝ)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hm ⊢
  rw [AEMeasurable.map_map_of_aemeasurable hm (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable]
  rfl

/-- Translation to the origin cube preserves the actual fixed-label trace law. -/
theorem coldNativeCellTrace_identDistrib (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    ProbabilityTheory.IdentDistrib (coldNativeCellTrace M m Q) (cutoffTraceDefect M m Q.scale)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  refine ⟨(coldNativeCellTrace_measurable M m Q).aemeasurable,
    (Variational.cutoffTraceDefect_measurable M m Q.scale).aemeasurable,?_⟩
  rw [coldNativeCellTrace_map]
  change _ = Measure.map (coldNativeCellTrace M m (originCube 2 Q.scale)) _
  rw [coldNativeCellTrace_map]
  exact Model.map_traceDefect_cube_eq_origin M m Q _

/-- Same-law native cell arrays inherit all finite moment bounds from their origin cell. -/
theorem coldNativeCellTrace_memLp_iff (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (p : ℝ≥0∞) :
    MemLp (coldNativeCellTrace M m Q) p (Cutoff.cutoffSampleLaw M).toMeasure ↔
      MemLp (cutoffTraceDefect M m Q.scale) p (Cutoff.cutoffSampleLaw M).toMeasure :=
  (coldNativeCellTrace_identDistrib M m Q).memLp_iff

/-- Exact equality of the actual cell and origin-cell real norms, at arbitrary p. -/
theorem coldNativeCellTrace_norm (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (p : ℝ≥0∞) :
    lpNorm (coldNativeCellTrace M m Q) p (Cutoff.cutoffSampleLaw M).toMeasure =
      lpNorm (cutoffTraceDefect M m Q.scale) p (Cutoff.cutoffSampleLaw M).toMeasure :=
  congrArg ENNReal.toReal ((coldNativeCellTrace_identDistrib M m Q).eLpNorm_eq (p := p))

end ASDExplicitGamma.Cold
