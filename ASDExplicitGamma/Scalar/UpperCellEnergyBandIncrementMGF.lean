module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandIncrementVariance
public import ASDExplicitGamma.Gaussian.SupMeanShellIncrementConcentration

/-! Exact full-band Gaussian tensor increment MGFs, with variance summed first. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

/-- The actual first tensor's centered increment MGF uses the summed physical
variance and the exact operator constant. Integrability is a conclusion. -/
theorem upper_cell_band_first_increment_mgf {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (x y : Vec 2) (lam : ℝ) :
    let X := fun (i : Fin 2) ω => upperCellBandJetScalar k w (Q3SpatialJet.first i) y ω-
      upperCellBandJetScalar k w (Q3SpatialJet.first i) x ω
    Integrable (fun ω => Real.exp (lam*(supMeanTensorNorm X ω-
      ∫ z,supMeanTensorNorm X z ∂(Cutoff.cutoffSampleLaw M).toMeasure)))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.exp (lam*(supMeanTensorNorm X ω-
      ∫ z,supMeanTensorNorm X z ∂(Cutoff.cutoffSampleLaw M).toMeasure))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.exp (lam^2*((waveEll2^2*upperCellBandVariance M h k w 2)*
        ((y-x) 0^2+(y-x) 1^2))/2) := by
  intro X
  let B := (waveEll2^2*upperCellBandVariance M h k w 2)*((y-x) 0^2+(y-x) 1^2)
  have hB : 0 ≤ B := by dsimp only [B,upperCellBandVariance]; positivity
  let C := Real.sqrt B
  have hCsq : C^2 = B := Real.sq_sqrt hB
  have hg : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure X :=
    supMean_gaussian_difference_family (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
      (fun i : Fin 2 => (Q3SpatialJet.first i,y)) (fun i : Fin 2 => (Q3SpatialJet.first i,x))
  have hv (a : Fin 2 → ℝ) :
      Var[(fun ω => ∑ i,a i*X i ω);(Cutoff.cutoffSampleLaw M).toMeasure] ≤ C^2*(∑ i,a i^2) := by
    rw [upper_cell_band_increment_variance M h hM k hk w]
    exact (upper_cell_band_first_projection_increment M h k w a x y).trans_eq
      (by rw [hCsq]; dsimp only [B]; ring)
  have hh := supMean_gaussian_tensor_mgf (Cutoff.cutoffSampleLaw M).toMeasure X hg C lam
    (Real.sqrt_nonneg _) hv
  simpa only [hCsq,B] using hh

/-- The actual second tensor's centered increment MGF uses the summed physical
variance and the exact operator constant. Integrability is a conclusion. -/
theorem upper_cell_band_second_increment_mgf {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (x y : Vec 2) (lam : ℝ) :
    let X := fun (i : Fin 2 × Fin 2) ω => upperCellBandJetScalar k w ((fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) i) y ω-
      upperCellBandJetScalar k w ((fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) i) x ω
    Integrable (fun ω => Real.exp (lam*(supMeanTensorNorm X ω-
      ∫ z,supMeanTensorNorm X z ∂(Cutoff.cutoffSampleLaw M).toMeasure)))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.exp (lam*(supMeanTensorNorm X ω-
      ∫ z,supMeanTensorNorm X z ∂(Cutoff.cutoffSampleLaw M).toMeasure))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.exp (lam^2*((waveEll3^2*upperCellBandVariance M h k w 3)*
        ((y-x) 0^2+(y-x) 1^2))/2) := by
  intro X
  let B := (waveEll3^2*upperCellBandVariance M h k w 3)*((y-x) 0^2+(y-x) 1^2)
  have hB : 0 ≤ B := by dsimp only [B,upperCellBandVariance]; positivity
  let C := Real.sqrt B
  have hCsq : C^2 = B := Real.sq_sqrt hB
  have hg : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure X :=
    supMean_gaussian_difference_family (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
      (fun i : Fin 2 × Fin 2 => ((fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) i,y)) (fun i : Fin 2 × Fin 2 => ((fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) i,x))
  have hv (a : Fin 2 × Fin 2 → ℝ) :
      Var[(fun ω => ∑ i,a i*X i ω);(Cutoff.cutoffSampleLaw M).toMeasure] ≤ C^2*(∑ i,a i^2) := by
    rw [upper_cell_band_increment_variance M h hM k hk w]
    exact (upper_cell_band_second_projection_increment M h k w a x y).trans_eq
      (by rw [hCsq]; dsimp only [B]; ring)
  have hh := supMean_gaussian_tensor_mgf (Cutoff.cutoffSampleLaw M).toMeasure X hg C lam
    (Real.sqrt_nonneg _) hv
  simpa only [hCsq,B] using hh

end
end ASDExplicitGamma.Scalar
