module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandKernelTrace

/-! Actual full-band tensor mean increments from summed covariance traces. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

/-- The actual first tensor's mean increment keeps the directional half-trace. -/
theorem upper_cell_band_first_mean_increment {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) (x y : Vec 2) :
    (∫ ω,‖upperCellBandTensor k w Q3SpatialJet.first y ω-upperCellBandTensor k w Q3SpatialJet.first x ω‖
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt ((waveTau2/2)*upperCellBandVariance M h k w 2*((y-x) 0^2+(y-x) 1^2)) := by
  have hg := supMean_gaussian_difference_family (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
    (fun i : Fin 2 => (Q3SpatialJet.first i,y)) (fun i : Fin 2 => (Q3SpatialJet.first i,x))
  have hh := supMean_gaussian_tensor_mean_le (Cutoff.cutoffSampleLaw M).toMeasure _ hg
  simp only [upper_cell_band_jet_difference_sq M h hM k hk w] at hh
  exact hh.trans (Real.sqrt_le_sqrt (upper_cell_band_first_increment_trace M h k w x y))


/-- The actual second tensor's mean increment keeps the directional half-trace. -/
theorem upper_cell_band_second_mean_increment {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) (x y : Vec 2) :
    (∫ ω,‖upperCellBandTensor k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) y ω-upperCellBandTensor k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) x ω‖
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt ((waveTau3/2)*upperCellBandVariance M h k w 3*((y-x) 0^2+(y-x) 1^2)) := by
  have hg := supMean_gaussian_difference_family (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
    (fun i : Fin 2 × Fin 2 => ((fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) i,y)) (fun i : Fin 2 × Fin 2 => ((fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) i,x))
  have hh := supMean_gaussian_tensor_mean_le (Cutoff.cutoffSampleLaw M).toMeasure _ hg
  simp only [upper_cell_band_jet_difference_sq M h hM k hk w] at hh
  exact hh.trans (Real.sqrt_le_sqrt (upper_cell_band_second_increment_trace M h k w x y))

end
end ASDExplicitGamma.Scalar
