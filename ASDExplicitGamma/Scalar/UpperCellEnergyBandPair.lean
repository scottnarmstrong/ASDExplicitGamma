module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandFields
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandStaticOperator

/-! Fixed observations and sharp covariance bounds for the complete band supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open TopologicalSpace Homogenization Gaussian Model MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
noncomputable section
section
variable (c : Vec 2) (s : ℝ) [Nonempty (supMeanClosedSquare c s)]

/-- The compact pair projection is literally a finite linear combination of
stored shell jets; its locations are not selected from the sample. -/
theorem upper_cell_band_pair_observation_eq {d : ℕ} (k : Fin d → ℤ) (w : Fin d → ℝ) (a b : ℝ) (n : ℕ) (j : Cutoff.CutoffSample 2) :
    supMeanCompactPairProjection (upperCellBandSquareTensor k w Q3SpatialJet.first c s j)
      (upperCellBandSquareTensor k w (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j) a b n =
    ∑ i, supMeanShellPairCoefficient a b n i *
      upperCellBandJetScalar k w (supMeanShellPairPoint c s n i).1 (supMeanShellPairPoint c s n i).2 j := by
  simp only [supMeanCompactPairProjection, supMeanCompactProjection,
    upperCellBandSquareTensor, ContinuousMap.coe_mk, upperCellBandTensor, upperCellBandJetScalar,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial,
    Fintype.sum_sum_type, supMeanShellPairPoint, supMeanShellPairCoefficient,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- The actual combined countable observations are jointly centered Gaussian. -/
theorem upper_cell_band_pair_gaussian {d : ℕ} (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : Fin d → ℤ) (hk : Function.Injective k) (w : Fin d → ℝ) (a b : ℝ) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (fun n j => supMeanCompactPairProjection (upperCellBandSquareTensor k w Q3SpatialJet.first c s j)
        (upperCellBandSquareTensor k w (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j) a b n) := by
  have hg := (upper_cell_band_scaled_jets_gaussian M h hM k hk w).finite_linear_image
    (supMeanShellPairPoint c s) (supMeanShellPairCoefficient a b)
  simpa only [upper_cell_band_pair_observation_eq] using! hg


/-- The exact sum of the two physical CM constants bounds every combined
countable observation; neither independence nor a common location is required. -/
theorem upper_cell_band_pair_kernel_norm {d : ℕ} (M : ABKModel 2) (h : ℝ) (k : Fin d → ℤ) (w : Fin d → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ‖∑ i, supMeanShellPairCoefficient a b n i •
      upperCellBandKernel M h k w (supMeanShellPairPoint c s n i).1
        (supMeanShellPairPoint c s n i).2‖ ≤
      a*Real.sqrt (waveEll1^2*upperCellBandVariance M h k w 1)+
      b*Real.sqrt (waveEll2^2*upperCellBandVariance M h k w 2) := by
  simp only [Fintype.sum_sum_type, supMeanShellPairPoint, supMeanShellPairCoefficient,
    mul_smul, ← Finset.smul_sum]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (upper_cell_band_first_kernel_projection M h k w _ _
      (supMean_norming_vector_norm_le _ _)) ha)
    (mul_le_mul_of_nonneg_left (upper_cell_band_second_kernel_projection M h k w _ _
      (supMean_norming_vector_norm_le _ _)) hb)

/-- All actual variances are bounded by the squared combined physical CM
constant, with the Gaussian law and kernel covariance instantiated internally. -/
theorem upper_cell_band_pair_projection_variance {d : ℕ} (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : Fin d → ℤ) (hk : Function.Injective k) (w : Fin d → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    Var[(fun j => supMeanCompactPairProjection (upperCellBandSquareTensor k w Q3SpatialJet.first c s j)
      (upperCellBandSquareTensor k w (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j) a b n);
        (Cutoff.cutoffSampleLaw M).toMeasure] ≤
      (a*Real.sqrt (waveEll1^2*upperCellBandVariance M h k w 1)+
      b*Real.sqrt (waveEll2^2*upperCellBandVariance M h k w 2))^2 := by
  simp_rw [upper_cell_band_pair_observation_eq]
  rw [supMean_gaussian_kernel_combination_variance _ _
    ((upper_cell_band_scaled_jets_gaussian M h hM k hk w).comp (supMeanShellPairPoint c s n))
    (fun i => upperCellBandKernel M h k w (supMeanShellPairPoint c s n i).1
      (supMeanShellPairPoint c s n i).2)
    (fun i j => upper_cell_band_kernel_covariance M h hM k hk w _ _ _ _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (upper_cell_band_pair_kernel_norm c s M h k w a b ha hb n) 2


end
end
end ASDExplicitGamma.Scalar
