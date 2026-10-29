module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandTensor
public import ASDExplicitGamma.Gaussian.SupMeanShellSupremum

/-! Actual compact full-band tensor fields for Gaussian chaining. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Section3
noncomputable section

/-- Spatial continuity follows from the stored C2 shell fields and finite sums. -/
theorem upper_cell_band_tensor_spatial_continuous {b : ℕ}
    (k : Fin b → ℤ) (w : Fin b → ℝ) {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) (ω : Cutoff.CutoffSample 2) :
    Continuous (fun x => upperCellBandTensor k w o x ω) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul (continuous_finsetSum _ (fun j _ =>
    continuous_const.mul (supMean_shell_jet_spatial_continuous (o i) (ω.val (k j)))))

/-- Each actual band tensor point is measurable on the original cutoff law. -/
theorem upper_cell_band_tensor_measurable {b : ℕ}
    (k : Fin b → ℤ) (w : Fin b → ℝ) {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) (x : Vec 2) : Measurable (upperCellBandTensor k w o x) := by
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr
    (fun i => (upper_cell_band_jet_measurable k w (supMeanJetObservation (o i) x)).const_mul _))

/-- Point integrability is derived from the actual joint Gaussian law. -/
theorem upper_cell_band_tensor_integrable {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) :
    Integrable (upperCellBandTensor k w o x) (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply memLp_one_iff_integrable.mp
  apply memLp_piLp_iff.mpr
  intro i
  exact (upper_cell_band_tensor_coordinates_gaussian M h hM k hk w o x).memLp i 1 (by simp)

/-- The compact full-band tensor is the literal finite sum on the physical square. -/
def upperCellBandSquareTensor {b : ℕ} (k : Fin b → ℤ) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (c : Vec 2) (s : ℝ)
    (ω : Cutoff.CutoffSample 2) : C(supMeanClosedSquare c s,EuclideanSpace ℝ ι) :=
  ⟨fun x => upperCellBandTensor k w o x.val ω,
    (upper_cell_band_tensor_spatial_continuous k w o ω).comp continuous_subtype_val⟩

end
end ASDExplicitGamma.Scalar
