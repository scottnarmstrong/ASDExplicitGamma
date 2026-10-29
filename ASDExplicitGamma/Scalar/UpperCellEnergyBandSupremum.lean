module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandPointMean
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandMeanIncrement
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandIncrementMGF
public import ASDExplicitGamma.Gaussian.SupMeanDyadicSupremum

/-! Full-band Gaussian chaining on the actual physical source square. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Section3
noncomputable section

/-- Full-band first-tensor supremum mean with exact physical derivative
variances. Its integrability and all increment estimates are proved internally. -/
theorem upper_cell_band_first_supremum_mean {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (c : Vec 2) (s : ℝ) (hs : 0 < s)
    (hV : 0 < upperCellBandVariance M h k w 2) :
    Integrable (fun ω => ‖upperCellBandSquareTensor k w Q3SpatialJet.first c s ω‖)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,‖upperCellBandSquareTensor k w Q3SpatialJet.first c s ω‖
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt (waveTau1*upperCellBandVariance M h k w 1)+
        (s*Real.sqrt (upperCellBandVariance M h k w 2))*
          (Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2) := by
  have hT : 0 ≤ waveTau2 := by
    norm_num [waveTau2,waveMu1,waveMu2,waveMu3,waveR1,waveR2,waveR3]
  have hA : 0 < waveEll2 := by
    simp only [waveEll2,waveR1,waveR2]
    positivity
  have hh := supMean_gaussian_square_supmean (Cutoff.cutoffSampleLaw M).toMeasure c s hs
    (fun ω x => upperCellBandTensor k w Q3SpatialJet.first x ω)
    (fun ω => upper_cell_band_tensor_spatial_continuous k w Q3SpatialJet.first ω)
    (fun x => upper_cell_band_tensor_integrable M h hM k hk w Q3SpatialJet.first x)
    (fun x => upper_cell_band_tensor_measurable k w Q3SpatialJet.first x)
    _ waveTau2 _ waveEll2 hT hV hA
    (upper_cell_band_first_tensor_mean M h hM k hk w c)
    (upper_cell_band_first_mean_increment M h hM k hk w) (by
      intro x y lam _
      simpa only [supMeanTensorNorm,upperCellBandTensor,upperCellBandJetScalar] using!
        upper_cell_band_first_increment_mgf M h hM k hk w x y lam)
  exact hh

/-- Full-band second-tensor supremum mean with exact physical derivative
variances. Its integrability and all increment estimates are proved internally. -/
theorem upper_cell_band_second_supremum_mean {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (c : Vec 2) (s : ℝ) (hs : 0 < s)
    (hV : 0 < upperCellBandVariance M h k w 3) :
    Integrable (fun ω => ‖upperCellBandSquareTensor k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) c s ω‖)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,‖upperCellBandSquareTensor k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) c s ω‖
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt (waveTau2*upperCellBandVariance M h k w 2)+
        (s*Real.sqrt (upperCellBandVariance M h k w 3))*
          (Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3) := by
  have hT : 0 ≤ waveTau3 := by
    norm_num [waveTau3,waveMu1,waveMu2,waveMu3,waveR1,waveR2,waveR3]
  have hA : 0 < waveEll3 := by
    simp only [waveEll3,waveMu3,waveR1,waveR2,waveR3]
    positivity
  have hh := supMean_gaussian_square_supmean (Cutoff.cutoffSampleLaw M).toMeasure c s hs
    (fun ω x => upperCellBandTensor k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) x ω)
    (fun ω => upper_cell_band_tensor_spatial_continuous k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) ω)
    (fun x => upper_cell_band_tensor_integrable M h hM k hk w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) x)
    (fun x => upper_cell_band_tensor_measurable k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) x)
    _ waveTau3 _ waveEll3 hT hV hA
    (upper_cell_band_second_tensor_mean M h hM k hk w c)
    (upper_cell_band_second_mean_increment M h hM k hk w) (by
      intro x y lam _
      simpa only [supMeanTensorNorm,upperCellBandTensor,upperCellBandJetScalar] using!
        upper_cell_band_second_increment_mgf M h hM k hk w x y lam)
  exact hh

end
end ASDExplicitGamma.Scalar
