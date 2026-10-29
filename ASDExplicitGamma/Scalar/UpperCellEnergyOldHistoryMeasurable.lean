module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldFreshSigma
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldHistory

/-! The actual complete trace history and its matrix majorant are OLD observables. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3
noncomputable section

theorem upper_cell_history_trace_old_measurable (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) :
    @Measurable _ _ (Cutoff.cutoffSampleLocalSigma M n Set.univ) _ (historyTrace M n Q) := by
  letI oldDomain : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n Set.univ
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n
  have hX : Measurable X := Model.measurable_coefficientCutoff_local_field M n
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

/-- The complete lagged trace history is measurable from completed OLD information. -/
theorem upper_cell_history_old_measurable (M : ABKModel 2) (n ell : ℤ) :
    @Measurable _ _ (Cutoff.cutoffSampleLocalSigma M n Set.univ) _ (lagTraceHistory M n ell) := by
  letI oldDomain : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n Set.univ
  have hd (j : ℕ) : Measurable (lagTraceMax M n ell j) :=
    history_finite_max_measurable _ _
      (fun Q => (upper_cell_history_trace_old_measurable M n Q).ennreal_ofReal)
  unfold lagTraceHistory
  exact (Measurable.tsum (fun j => (hd j).const_mul _)).const_mul _

/-- The physical majorant is OLD; the real conversion is the one already
identified with the finite physical trace history. -/
theorem upper_cell_majorant_old_measurable (M : ABKModel 2) (n ell : ℤ) :
    @Measurable _ _ (Cutoff.cutoffSampleLocalSigma M n Set.univ) _
      (fun ω => 1+2*(lagTraceHistory M n ell ω).toReal+
        Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)) := by
  letI oldDomain : MeasurableSpace (Cutoff.CutoffSample 2) := Cutoff.cutoffSampleLocalSigma M n Set.univ
  have hh := (upper_cell_history_old_measurable M n ell).ennreal_toReal
  exact (measurable_const.add (hh.const_mul 2)).add ((hh.const_mul 2).sqrt)

end
end ASDExplicitGamma.Scalar
