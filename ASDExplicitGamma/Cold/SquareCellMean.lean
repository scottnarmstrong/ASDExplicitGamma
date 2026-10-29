module

public import ASDExplicitGamma.Cold.SquarePartitionProjection

/-! # Finite cell averages and expectations of genuine integrated energies -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Cell averages preserve constants. -/
theorem squareCellMean_const (Q : TriadicCube 2) (r : ℕ) (c : ℝ) :
    squareCellMean Q r (fun _ => c) = c := by
  have hn : (descendantsAtDepth Q r).card ≠ 0 :=
    Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q r)
  simp only [squareCellMean,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  field_simp

/-- Cell averages commute with subtraction. -/
theorem squareCellMean_sub (Q : TriadicCube 2) (r : ℕ) (f g : SquareCells Q r → ℝ) :
    squareCellMean Q r (fun R => f R-g R) = squareCellMean Q r f-squareCellMean Q r g := by
  unfold squareCellMean
  rw [Finset.sum_sub_distrib]
  ring

/-- Cell averages commute with a finite load sum. -/
theorem squareCellMean_sum (Q : TriadicCube 2) (r : ℕ) {ι : Type*} (S : Finset ι)
    (f : ι → SquareCells Q r → ℝ) :
    squareCellMean Q r (fun R => ∑ i ∈ S, f i R) = ∑ i ∈ S, squareCellMean Q r (f i) := by
  unfold squareCellMean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Pointwise order of actual cell energies is preserved by averaging. -/
theorem squareCellMean_mono (Q : TriadicCube 2) (r : ℕ) {f g : SquareCells Q r → ℝ}
    (h : ∀ R, f R ≤ g R) : squareCellMean Q r f ≤ squareCellMean Q r g := by
  unfold squareCellMean
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R _ => h R) (by positivity)

/-- A finite cell average is integrable when every actual integrated cell energy is. -/
theorem integrable_squareCellMean {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    (Q : TriadicCube 2) (r : ℕ) {f : Ω → SquareCells Q r → ℝ}
    (hf : ∀ R, Integrable (fun ω => f ω R) ℙ) :
    Integrable (fun ω => squareCellMean Q r (f ω)) ℙ :=
  (integrable_finsetSum _ (fun R _ => hf R)).const_mul _

/-- Expectation commutes with the actual finite cell average. -/
theorem integral_squareCellMean {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    (Q : TriadicCube 2) (r : ℕ) {f : Ω → SquareCells Q r → ℝ}
    (hf : ∀ R, Integrable (fun ω => f ω R) ℙ) :
    (∫ ω, squareCellMean Q r (f ω) ∂ℙ) = squareCellMean Q r (fun R => ∫ ω, f ω R ∂ℙ) := by
  unfold squareCellMean
  rw [integral_const_mul, integral_finsetSum _ (fun R _ => hf R)]

/-- The actual cutoff's cell means, discounted by its oscillation charge, average to `7/8`. -/
theorem squareCellMean_plateau_comparison_weights (Q : TriadicCube 2) (r : ℕ) :
    squareCellMean Q r (fun R => cubeAverage R.val (plateauOnSquare Q) - (1/8 : ℝ)) = 7/8 := by
  rw [squareCellMean_sub, squareCellMean_const]
  have hφ : IntegrableOn (plateauOnSquare Q) (openCubeSet Q) :=
    (MemLp.of_bound (lipschitzWith_plateauOnSquare Q).continuous.aestronglyMeasurable
      (12/7) (Filter.Eventually.of_forall (norm_plateauOnSquare_le Q)) :
      MemLp (plateauOnSquare Q) 1 (volume.restrict (openCubeSet Q))).integrable (by simp)
  have hm := squareCellMean_volumeAverage Q r hφ
  simp_rw [square_volumeAverage_eq_cubeAverage] at hm
  rw [hm, cubeAverage_eq_integral_normalizedCubeMeasure, integral_plateauOnSquare]
  norm_num

end ASDExplicitGamma.Cold
