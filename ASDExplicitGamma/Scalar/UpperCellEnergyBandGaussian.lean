module

public import ASDExplicitGamma.Scalar.UpperCellEnergyGaussianSum
public import ASDExplicitGamma.Gaussian.DerivativeLawQ3
public import ASDExplicitGamma.Gaussian.BandModelLaw

/-! The literal weighted finite fresh band has joint Gaussian stored jets. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

/-- The actual finite-band scalar value, first or second derivative observation.
It is formed from the stored shell derivatives on the original cutoff sample. -/
def upperCellBandJet {b : ℕ} (k : Fin b → ℤ) (w : Fin b → ℝ)
    (o : ShellDerivativeObservation) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i,w i*shellDerivativeEval o (ω.val (k i))

/-- Each stored band observation is measurable on the actual cutoff carrier. -/
theorem upper_cell_band_jet_measurable {b : ℕ} (k : Fin b → ℤ) (w : Fin b → ℝ)
    (o : ShellDerivativeObservation) : Measurable (upperCellBandJet k w o) := by
  exact Finset.measurable_sum _ (fun i _ =>
    ((shellDerivativeEval_continuous o).measurable.comp
      ((measurable_pi_apply (k i)).comp measurable_subtype_coe)).const_mul _)

/-- Exact shell marginal under the full cutoff sample law. -/
theorem upper_cell_shell_marginal (M : ABKModel 2) (k : ℤ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (fun ω => ω.val k) =
      (ShellField.shellMarginalLaw M.P k).toMeasure := by
  have hh := congrArg (fun μ : Measure (Cutoff.ShellSeq 2) => μ.map (fun ω => ω k))
    (Cutoff.map_cutoffSampleLaw_val M)
  rw [Measure.map_map (measurable_pi_apply k) measurable_subtype_coe] at hh
  exact hh

/-- All finite cross-point and mixed-derivative observations of the weighted
band are jointly centered Gaussian. Shell covariance is combined before norms;
no independence of different observations of this band is asserted. -/
theorem upper_cell_band_jets_gaussian {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellBandJet k w) := by
  let X := fun i : Fin b => fun ω : Cutoff.CutoffSample 2 => ω.val (k i)
  have hX (i : Fin b) : Measurable (X i) :=
    (measurable_pi_apply (k i)).comp measurable_subtype_coe
  have hi : iIndepFun X (Cutoff.cutoffSampleLaw M).toMeasure :=
    iIndepFun_of_map _ _ Subtype.val measurable_subtype_coe
      (Cutoff.map_cutoffSampleLaw_val M) (fun i ω => ω (k i))
      (fun i => measurable_pi_apply (k i)) ((Model.shellLevels_independent M).precomp hk)
  have hg (i : Fin b) : IsCenteredGaussianFamily
      ((Cutoff.cutoffSampleLaw M).toMeasure.map (X i)) shellDerivativeEval := by
    rw [show (Cutoff.cutoffSampleLaw M).toMeasure.map (X i) =
      (ShellField.shellMarginalLaw M.P (k i)).toMeasure from upper_cell_shell_marginal M (k i)]
    exact q3Shell_stored_derivatives_gaussian M h hM (k i)
  exact upper_cell_independent_gaussian_family_sum _ X hX hi shellDerivativeEval
    (fun o => (shellDerivativeEval_continuous o).measurable) hg Finset.univ w

end
end ASDExplicitGamma.Scalar
