module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetGaussianSquares
public import ASDExplicitGamma.Triadic.PoincareCell
public import Algsuperdiff.Section3.Provider.Corrector.RealizationTransfer
public import Algsuperdiff.Section3.Provider.Corrector.StationaryStrip

/-! Physical cube averaging for the actual stationary RESET gradient rows. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open scoped ENNReal
noncomputable section

/-- Real L2 norm in terms of the actual second moment. -/
theorem upper_cell_reset_lp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ) :
    lpNorm X 2 μ = Real.sqrt (∫ ω, (X ω)^2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hX]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  exact (Real.sqrt_eq_rpow _).symm

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- Physical cube averaging contracts L2 on the original stationary carrier. -/
theorem upper_cell_reset_stationary_average_L2
    (Q : TriadicCube d) {X : Ω → ℝ} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    MemLp (fun ω => cubeAverage Q (realize X ω)) 2 μ ∧
      lpNorm (fun ω => cubeAverage Q (realize X ω)) 2 μ ≤ lpNorm X 2 μ := by
  have hAm : StronglyMeasurable (fun ω => cubeAverage Q (realize X ω)) := by
    unfold cubeAverage
    exact ((stronglyMeasurable_uncurry_realize hXm).integral_prod_right'
      (ν := volume.restrict (cubeSet Q))).const_mul _
  have hB : Integrable (fun ω => cubeAverage Q (fun x => ‖realize X ω x‖^2)) μ := by
    exact (integrable_setIntegral_normSq_realize (μ := μ) (volume_cubeSet_lt_top Q).ne hXm hX).const_mul _
  have ht : (∫ ω, cubeAverage Q (fun x => ‖realize X ω x‖^2) ∂μ) =
      ∫ ω, (X ω)^2 ∂μ := by
    unfold cubeAverage
    rw [integral_const_mul, integral_setIntegral_normSq_realize (volume_cubeSet_lt_top Q).ne hXm hX,
      volume_cubeSet_toReal, ← mul_assoc, inv_mul_cancel₀ (cubeVolume_pos Q).ne', one_mul]
    simp only [Real.norm_eq_abs, sq_abs]
  have hp : ∀ᵐ ω ∂μ, (cubeAverage Q (realize X ω))^2 ≤
      cubeAverage Q (fun x => ‖realize X ω x‖^2) := by
    filter_upwards [ae_memLp_two_realize (μ := μ) (volume_openCubeSet_lt_top Q).ne hXm hX] with ω hω
    have hn := memLp_normalized_of_memL2On hω
    have hh := energy_projection_le Q 0 hn
    rw [energy_projection_zero] at hh
    simpa only [energy, pairing, ← pow_two, Real.norm_eq_abs, sq_abs] using hh
  have hA2 : Integrable (fun ω => (cubeAverage Q (realize X ω))^2) μ := by
    apply hB.mono' (hAm.pow 2).aestronglyMeasurable
    filter_upwards [hp] with ω hω
    change ‖(cubeAverage Q (realize X ω))^2‖ ≤ _
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  have hA : MemLp (fun ω => cubeAverage Q (realize X ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hAm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hA2
  refine ⟨hA, ?_⟩
  rw [upper_cell_reset_lp_two μ _ hAm.aestronglyMeasurable,
    upper_cell_reset_lp_two μ X hX.aestronglyMeasurable]
  apply Real.sqrt_le_sqrt
  exact (integral_mono_ae hA2 hB hp).trans_eq ht

/-- A spatial cube average of a centered Gaussian square retains the exact
sqrt-three L2 payment without assuming independence across points. -/
theorem upper_cell_reset_gaussian_spatial_square_L2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
    {μ : Measure Ω} [SFinite μ] [MeasurableConstVAdd (Vec d) Ω]
    [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]
    (Q : TriadicCube d) {X : Ω → ℝ} (hXm : StronglyMeasurable X)
    (hX : ProbabilityTheory.HasGaussianLaw X μ) (hm : ∫ ω, X ω ∂μ = 0) :
    MemLp (fun ω => cubeAverage Q (fun x => (realize X ω x)^2)) 2 μ ∧
      lpNorm (fun ω => cubeAverage Q (fun x => (realize X ω x)^2)) 2 μ ≤
        Real.sqrt 3 * (∫ ω, (X ω)^2 ∂μ) := by
  have hs := upper_cell_reset_gaussian_square_L2 μ X hX hm
  have ha := upper_cell_reset_stationary_average_L2 Q (hXm.pow 2) hs.1
  refine ⟨ha.1, ?_⟩
  exact ha.2.trans_eq hs.2

/-- A finite family of correlated Gaussian gradient coordinates has the same
sqrt-three spatial L2 payment coordinate by coordinate. -/
theorem upper_cell_reset_gaussian_spatial_vector_L2
    {d : ℕ} {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    [AddAction (Vec d) Ω] {μ : Measure Ω} [SFinite μ]
    [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
    [VAddInvariantMeasure (Vec d) Ω μ]
    (Q : TriadicCube d) (X : I → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i))
    (hX : ∀ i, ProbabilityTheory.HasGaussianLaw (X i) μ)
    (hm : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    MemLp (fun ω => ∑ i, cubeAverage Q (fun x => (realize (X i) ω x)^2)) 2 μ ∧
      lpNorm (fun ω => ∑ i, cubeAverage Q (fun x => (realize (X i) ω x)^2)) 2 μ ≤
        Real.sqrt 3 * ∑ i, ∫ ω, (X i ω)^2 ∂μ := by
  have hs (i) := upper_cell_reset_gaussian_spatial_square_L2 Q (hXm i) (hX i) (hm i)
  have hmem : MemLp (fun ω => ∑ i, cubeAverage Q (fun x => (realize (X i) ω x)^2)) 2 μ :=
    memLp_finsetSum _ (fun i _ => (hs i).1)
  refine ⟨hmem, ?_⟩
  have hn := lpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => (hs i).1)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have heq : (∑ i, (fun ω => cubeAverage Q (fun x => (realize (X i) ω x)^2))) =
      (fun ω => ∑ i, cubeAverage Q (fun x => (realize (X i) ω x)^2)) := by
    funext ω
    exact Finset.sum_apply ω Finset.univ _
  rw [heq] at hn
  exact hn.trans ((Finset.sum_le_sum (fun i _ => (hs i).2)).trans_eq
    (Finset.mul_sum _ _ _).symm)

end
end ASDExplicitGamma.Scalar
