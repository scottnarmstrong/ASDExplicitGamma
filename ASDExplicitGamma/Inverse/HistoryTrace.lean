module

public import ASDExplicitGamma.Inverse.HistoryPopulation
public import ASDExplicitGamma.Variational.TrueFrame

/-! Trace histories of the actual completed cutoff, always in its true running frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def historyTrace (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun (Annealed.sigmaBar M n : ℝ)

theorem history_trace_nonneg (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ historyTrace M n Q ω := by
  obtain ⟨Λ,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M n ω Q
  exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
    (Annealed.sigmaBar_characterization M n).1

/-- The existing literal coarse-entry measurability proof applies on every source cube. -/
theorem history_trace_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    Measurable (historyTrace M n Q) := by
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n
  have hX : Measurable X := Cutoff.measurable_coefficientCutoff M.nu n
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    fun ω => Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω
  have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet hX hEll Q
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet hX hEll Q
  have hTraceUL : Measurable (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ, (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i)
  have hTraceLR : Measurable (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ, (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i)
  exact ((hTraceUL.const_mul _).add (hTraceLR.const_mul _)).sub measurable_const

theorem history_trace_norm_pushforward (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    eLpNorm (historyTrace M n Q) 20 (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun (Annealed.sigmaBar M n : ℝ))
        20 (Cutoff.coefficientCutoffLaw M n) := by
  have hi := Variational.integrable_traceDefect_cutoffLaw M n Q (Annealed.sigmaBar M n : ℝ)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  symm
  exact eLpNorm_map_measure hi.aestronglyMeasurable (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable

/-- Translation preserves the L20 norm at the same cutoff and true frame. -/
theorem history_trace_norm_origin (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    eLpNorm (historyTrace M n Q) 20 (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (cutoffTraceDefect M n Q.scale) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hQ := Model.aemeasurable_traceDefect_cutoffLaw M n Q (Annealed.sigmaBar M n : ℝ)
  have hO := Model.aemeasurable_traceDefect_cutoffLaw M n (originCube 2 Q.scale) (Annealed.sigmaBar M n : ℝ)
  rw [history_trace_norm_pushforward]
  have hnormQ := eLpNorm_map_measure (μ := Cutoff.coefficientCutoffLaw M n) (p := (20:ℝ≥0∞))
    (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable hQ
  have hnormO := eLpNorm_map_measure (μ := Cutoff.coefficientCutoffLaw M n) (p := (20:ℝ≥0∞))
    (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable hO
  have hmap := Model.map_traceDefect_cube_eq_origin M n Q (Annealed.sigmaBar M n : ℝ)
  rw [hmap] at hnormQ
  have hsame := hnormQ.symm.trans hnormO
  have hp := history_trace_norm_pushforward M n (originCube 2 Q.scale)
  exact hsame.trans hp.symm

/-- Passing to the nonnegative extended trace changes no probability norm. -/
theorem history_trace_ofReal_norm (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    eLpNorm (fun ω => ENNReal.ofReal (historyTrace M n Q ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (cutoffTraceDefect M n Q.scale) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have he : (fun ω => ENNReal.ofReal (historyTrace M n Q ω)) = (fun ω => ‖historyTrace M n Q ω‖ₑ) := by
    funext ω
    exact (Real.enorm_eq_ofReal (history_trace_nonneg M n Q ω)).symm
  rw [he,eLpNorm_enorm _ (history_trace_measurable M n Q).aestronglyMeasurable]
  exact history_trace_norm_origin M n Q

end ASDExplicitGamma.Inverse
