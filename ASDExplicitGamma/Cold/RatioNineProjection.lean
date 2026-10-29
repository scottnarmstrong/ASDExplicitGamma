module

public import ASDExplicitGamma.Cold.SquareGradientProjection

/-! # The actual ratio-nine martingale blocks -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Coordinatewise cell projection of an actual vector field. -/
def squareProjection (Q : TriadicCube 2) (r : ℕ) (G : Vec 2 → Vec 2) : Vec 2 → Vec 2 :=
  fun x i => cubeProjection Q r (fun y => G y i) x

/-- The top block is depth two; successive blocks have side ratio nine. -/
def ratioNineBlock (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (k : ℕ) : Vec 2 → Vec 2 :=
  if k = 0 then squareProjection Q 2 G else
    fun x => squareProjection Q (2*k+2) G x - squareProjection Q (2*k) G x

/-- All blocks are genuine square-integrable step fields. -/
theorem ratioNineBlock_memLp (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (k : ℕ) (i : Fin 2) :
    MemLp (fun x => ratioNineBlock Q G k x i) 2 (normalizedCubeMeasure Q) := by
  unfold ratioNineBlock
  split_ifs
  · exact projection_memLp Q 2 _ 2
  · exact (projection_memLp Q (2*k+2) _ 2).sub (projection_memLp Q (2*k) _ 2)

/-- The actual coarse projection of each non-top block vanishes. -/
theorem ratioNineBlock_projection_zero (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    {k : ℕ} (hk : k ≠ 0) (i : Fin 2) :
    cubeProjection Q (2*k) (fun x => ratioNineBlock Q G k x i) = 0 := by
  simp only [ratioNineBlock, ite_eq_right hk, squareProjection, Pi.sub_apply]
  have heq : (fun x => cubeProjection Q (2*k+2) (fun y => G y i) x -
      cubeProjection Q (2*k) (fun y => G y i) x) =
      (fun x => cubeProjection Q (2*k+2) (fun y => G y i) x +
        (-1) * cubeProjection Q (2*k) (fun y => G y i) x) := by funext x; ring
  rw [heq, projection_add Q _ (projection_memLp Q _ _ 2)
    ((projection_memLp Q _ _ 2).const_mul _), projection_smul,
    projection_projection_of_le Q (by omega) (hG i), projection_idempotent]
  funext x
  simp

/-- Block energies are the increments of the actual projected energies. -/
theorem ratioNineBlock_energy (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    {k : ℕ} (hk : k ≠ 0) :
    squareVectorEnergy Q (ratioNineBlock Q G k) =
      squareVectorEnergy Q (squareProjection Q (2*k+2) G) -
        squareVectorEnergy Q (squareProjection Q (2*k) G) := by
  unfold squareVectorEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := energy_residual Q (2*k) (projection_memLp Q (2*k+2) (fun x => G x i) 2)
  rw [projection_projection_of_le Q (by omega) (hG i)] at h
  simpa only [ratioNineBlock, ite_eq_right hk, squareProjection, Pi.sub_apply] using h

/-- Finite block sums telescope literally to the finer cell projection. -/
theorem sum_ratioNineBlock (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), ratioNineBlock Q G k) = squareProjection Q (2*N+2) G := by
  induction N with
  | zero => simp [ratioNineBlock]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [ratioNineBlock, ite_eq_right (Nat.succ_ne_zero N)]
    have heq : 2 * (N + 1) = 2*N+2 := by omega
    rw [heq]
    funext x i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- Convert actual normalized coordinate L² hypotheses to the variational solver's domain. -/
theorem memVectorL2_of_normalized (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    MemVectorL2 (openCubeSet Q) G := by
  exact memLp_pi_iff.mpr (fun i => memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i))

/-- The actual mean-zero potential of each ratio-nine source block. -/
def ratioNinePotential (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (k : ℕ) :
    H1Function (openCubeSet Q) :=
  (squareGradientPotential Q (memVectorL2_of_normalized Q (ratioNineBlock_memLp Q G k))).toH1Function

/-- The defining weak Neumann equation of a block potential. -/
theorem ratioNinePotential_primitive (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (k : ℕ) :
    Support.Localization.IsNeumannPrimitive Q (ratioNineBlock Q G k) (ratioNinePotential Q G k) :=
  squareGradientPotential_isNeumannPrimitive Q _

/-- Its actual gradient energy is contracted from its source block energy. -/
theorem ratioNinePotential_energy_le (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (k : ℕ) :
    squareVectorEnergy Q (ratioNinePotential Q G k).grad ≤
      squareVectorEnergy Q (ratioNineBlock Q G k) := squareGradientPotential_energy_le Q _

end ASDExplicitGamma.Cold
