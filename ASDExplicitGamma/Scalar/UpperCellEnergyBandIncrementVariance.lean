module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandKernelOperator
public import ASDExplicitGamma.Gaussian.SupMeanGaussianKernelVariance

/-! Actual Gaussian projection variances of full-band tensor increments. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- Every finite projection of an actual band tensor increment has exactly
the variance of its direct-sum Hilbert kernel. -/
theorem upper_cell_band_increment_variance {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (a : ι → ℝ) (x y : Vec 2) :
    Var[(fun ω => ∑ i,a i*(upperCellBandJetScalar k w (o i) y ω-
      upperCellBandJetScalar k w (o i) x ω));(Cutoff.cutoffSampleLaw M).toMeasure] =
      ‖∑ i,a i • (upperCellBandKernel M h k w (o i) y-
        upperCellBandKernel M h k w (o i) x)‖^2 := by
  have hg := supMean_gaussian_difference_family (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
    (fun i => (o i,y)) (fun i => (o i,x))
  apply supMean_gaussian_kernel_combination_variance _ _ hg
  intro i j
  exact supMean_gaussian_kernel_difference_covariance (Cutoff.cutoffSampleLaw M).toMeasure
    (fun p : Q3SpatialJet × Vec 2 => upperCellBandJetScalar k w p.1 p.2)
    (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
    (fun p : Q3SpatialJet × Vec 2 => upperCellBandKernel M h k w p.1 p.2)
    (fun p q => upper_cell_band_kernel_covariance M h hM k hk w p.1 q.1 p.2 q.2)
    (o i,y) (o i,x) (o j,y) (o j,x)

end
end ASDExplicitGamma.Scalar
