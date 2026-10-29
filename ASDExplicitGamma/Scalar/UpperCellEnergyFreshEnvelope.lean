module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldFreshSigma
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalEnvelope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Fresh measurability of the literal full-band compact derivative envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model Algsuperdiff.Section3
noncomputable section

/-- Stored finite-band jets use only the indicated fresh shell coordinates. -/
theorem upper_cell_band_jet_fresh_measurable {b : ℕ}
    (n : ℤ) (k : Fin b → ℤ) (hk : ∀ i, n<k i) (w : Fin b → ℝ) (o : ShellDerivativeObservation) :
    @Measurable _ _ (upperCellFreshSigma n) _ (upperCellBandJet k w o) := by
  letI freshDomain : MeasurableSpace (Cutoff.CutoffSample 2) := upperCellFreshSigma n
  exact Finset.measurable_sum _ (fun i _ =>
    ((shellDerivativeEval_continuous o).measurable.comp
      (upper_cell_shell_fresh_measurable n (k i) (hk i))).const_mul _)

/-- Pointwise full tensors retain the same fresh measurability. -/
theorem upper_cell_band_tensor_fresh_measurable {b : ℕ}
    (n : ℤ) (k : Fin b → ℤ) (hk : ∀ i, n<k i) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) :
    @Measurable _ _ (upperCellFreshSigma n) _ (upperCellBandTensor k w o x) := by
  letI freshDomain : MeasurableSpace (Cutoff.CutoffSample 2) := upperCellFreshSigma n
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr
    (fun i => (upper_cell_band_jet_fresh_measurable n k hk w
      (supMeanJetObservation (o i) x)).const_mul _))

/-- The entire compact tensor is a fresh random element, not merely each
of a selected finite set of evaluations. -/
theorem upper_cell_band_square_fresh_measurable {b : ℕ}
    (n : ℤ) (k : Fin b → ℤ) (hk : ∀ i, n<k i) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (c : Vec 2) (s : ℝ) :
    @Measurable _ _ (upperCellFreshSigma n) _ (upperCellBandSquareTensor k w o c s) := by
  letI freshDomain : MeasurableSpace (Cutoff.CutoffSample 2) := upperCellFreshSigma n
  apply ContinuousMap.measurable_iff_eval.mpr
  intro x
  exact upper_cell_band_tensor_fresh_measurable n k hk w o x.val

/-- The correlated pair of compact gradient/Hessian suprema is paid through
one observable measurable from all the fresh shells. -/
theorem upper_cell_band_envelope_fresh_measurable {b : ℕ}
    (n : ℤ) (k : Fin b → ℤ) (hk : ∀ i, n<k i) (w : Fin b → ℝ)
    (c : Vec 2) (s a b' : ℝ) :
    @Measurable _ _ (upperCellFreshSigma n) _ (upperCellBandEnvelope k w c s a b') := by
  letI freshDomain : MeasurableSpace (Cutoff.CutoffSample 2) := upperCellFreshSigma n
  exact ((upper_cell_band_square_fresh_measurable n k hk w Q3SpatialJet.first c s).norm.const_mul a).add
    ((upper_cell_band_square_fresh_measurable n k hk w
      (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) c s).norm.const_mul b')

/-- The exact physical normalized envelope is fresh, for every height. -/
theorem upper_cell_physical_envelope_fresh_measurable
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (c : Vec 2) :
    @Measurable _ _ (upperCellFreshSigma n) _ (upperCellPhysicalEnvelope M n height c) := by
  apply upper_cell_band_envelope_fresh_measurable
  intro i
  dsimp [upperCellPhysicalBandLabel]
  omega

end
end ASDExplicitGamma.Scalar
