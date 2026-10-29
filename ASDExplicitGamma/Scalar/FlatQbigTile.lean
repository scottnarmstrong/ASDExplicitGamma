module

public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! Q_big flat successor, deterministic tile layer: the depth-`n` tiled Poincaré inequality
for the positive Haar energy of an `H¹` vector field on a parent cube. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

noncomputable section

/-- The side of a depth-134 tile of `Q` (the Poincare scale of the tiled energy). -/
def tileSide (Q : TriadicCube 2) : ℝ := cubeScaleFactor Q / 3 ^ 134

theorem tileSide_pos (Q : TriadicCube 2) : 0 < tileSide Q :=
  div_pos (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q) (by positivity)

theorem descendantsAverage_add' (Q : TriadicCube 2) (n : ℕ) (f g : TriadicCube 2 → ℝ) :
    descendantsAverage Q n (fun R => f R + g R) =
      descendantsAverage Q n f + descendantsAverage Q n g := by
  show (((descendantsAtDepth Q n).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q n, (f R + g R)) =
    ((descendantsAtDepth Q n).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q n, f R +
      ((descendantsAtDepth Q n).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q n, g R
  rw [Finset.sum_add_distrib, mul_add]

theorem descendantsAverage_const_mul' (Q : TriadicCube 2) (n : ℕ) (K : ℝ)
    (f : TriadicCube 2 → ℝ) :
    descendantsAverage Q n (fun R => K * f R) = K * descendantsAverage Q n f := by
  show (((descendantsAtDepth Q n).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q n, K * f R) =
    K * (((descendantsAtDepth Q n).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q n, f R)
  rw [← Finset.mul_sum]
  ring

theorem descendantsAverage_affine (Q : TriadicCube 2) (n : ℕ)
    (E : Fin 2 → TriadicCube 2 → ℝ) (H : Fin 2 → Fin 2 → TriadicCube 2 → ℝ) (K : ℝ) :
    descendantsAverage Q n (fun R => (∑ i, E i R) + K * ∑ i, ∑ j, H i j R) =
      (∑ i, descendantsAverage Q n (E i)) +
        K * ∑ i, ∑ j, descendantsAverage Q n (H i j) := by
  rw [descendantsAverage_add', descendantsAverage_const_mul',
    descendantsAverage_sum, descendantsAverage_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  exact descendantsAverage_sum (fun j => H i j)

/-- Tiled Poincaré: the tile-averaged positive Haar energy of an `H¹` field on `Q` is at most
its `L²` energy on `Q` plus the Poincaré constant at the tile side times the gradient energy. -/
theorem tiled_positiveHaar_le_l2_add_gradient (Q : TriadicCube 2) (n : ℕ)
    (F : Vec 2 → Fin 2 → ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 (normalizedCubeMeasure Q))
    (hweak : ∀ i, HasWeakGradientOn (openCubeSet Q) (fun x => F x i) (fun x j => G x i j)) :
    lemmaVTiledPositiveEnergy Q n F ≤
      (∑ i, energy Q (fun x => F x i)) +
        (467 / 1000 : ℝ) ^ 2 * (cubeScaleFactor Q / 3 ^ n) ^ 2 *
          ∑ i, ∑ j, energy Q (fun x => G x i j) := by
  have hcell : ∀ R ∈ descendantsAtDepth Q n,
      vectorPositiveHaarEnergy R F ≤
        (∑ i, energy R (fun x => F x i)) +
          (467 / 1000 : ℝ) ^ 2 * (cubeScaleFactor Q / 3 ^ n) ^ 2 *
            ∑ i, ∑ j, energy R (fun x => G x i j) := by
    intro R hR
    have hmeas : MeasurableSet (openCubeSet Q) := (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
    have hsub : openCubeSet R ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    have h := vector_positiveHaarNorm_sq_le_l2_add_gradient R F G
      (fun i => memLp_on_descendant_of_memLp hR (hF i))
      (fun i j => memLp_on_descendant_of_memLp hR (hG i j))
      (fun i => hasWeakGradientOn_mono hsub hmeas (hweak i))
    rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR] at h
    have hnn : vectorPositiveHaarEnergy R F = vectorPositiveHaarNorm R F ^ 2 := by
      unfold vectorPositiveHaarNorm
      rw [Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg R F)]
    rw [hnn]; exact h
  unfold lemmaVTiledPositiveEnergy
  refine (descendantsAverage_le hcell).trans (le_of_eq ?_)
  rw [descendantsAverage_affine]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact (energy_eq_descendantsAverage Q n (hF i)).symm
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact (energy_eq_descendantsAverage Q n (hG i j)).symm

end

end ASDExplicitGamma.Scalar
