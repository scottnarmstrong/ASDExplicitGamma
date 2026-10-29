module

public import ASDExplicitGamma.Scalar.UpperCellEnergyFreshPotentialMean
public import ASDExplicitGamma.Scalar.UpperCellEnergyFreshEnvelope
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldHistoryMeasurable

/-! Independence for the actual physical load and compact band envelope.
The two fresh quantities remain a joint observable throughout. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Inverse Algsuperdiff.Section3
noncomputable section

/-- Euclidean magnitude of the principal load with a unit first component
and the literal spatially averaged potential correction as second component. -/
def upperCellPhysicalLoadMagnitude (M : ABKModel 2) (n terminal : ℤ)
    (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (1 + ∑ i : Fin 2, (upperCellPhysicalPotentialMean M n terminal c e Q ω i)^2)

theorem upper_cell_physical_load_magnitude_nonneg
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    0 ≤ upperCellPhysicalLoadMagnitude M n terminal c e Q ω := Real.sqrt_nonneg _

theorem upper_cell_physical_load_magnitude_fresh_measurable
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    @Measurable _ _ (upperCellFreshSigma n) _
      (upperCellPhysicalLoadMagnitude M n terminal c e Q) := by
  letI freshDomain : MeasurableSpace (Cutoff.CutoffSample 2) := upperCellFreshSigma n
  exact (measurable_const.add (Finset.measurable_sum _ (fun i _ =>
    (upper_cell_physical_potential_mean_fresh_measurable M n terminal c e Q i).pow_const 2))).sqrt

/-- OLD history is independent of the joint physical fresh envelope and load.
There is no independence premise, and no assertion that envelope and load
are independent of each other. -/
theorem upper_cell_physical_majorant_pair_independent
    (M : ABKModel 2) (n ell : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    IndepFun
      (fun ω => 1+2*(lagTraceHistory M n ell ω).toReal+
        Real.sqrt (2*(lagTraceHistory M n ell ω).toReal))
      (fun ω => (upperCellPhysicalEnvelope M n height (cubeCenter Q) ω,
        upperCellPhysicalLoadMagnitude M n (n+height) c e Q ω))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply upper_cell_old_fresh_observables_independent M n
  · exact upper_cell_majorant_old_measurable M n ell
  · exact (upper_cell_physical_envelope_fresh_measurable M n height (cubeCenter Q)).prodMk
      (upper_cell_physical_load_magnitude_fresh_measurable M n (n+height) c e Q)

end
end ASDExplicitGamma.Scalar
