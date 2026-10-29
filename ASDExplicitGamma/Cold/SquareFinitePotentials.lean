module

public import ASDExplicitGamma.Cold.SquareProjectionLimit

/-! # Finite sums of actual gradient-projection potentials -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Additivity of the vector spatial pairing. -/
theorem vectorPairing_add_left (Q : TriadicCube 2) {F G H : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q (F + G) H = vectorPairing Q F H + vectorPairing Q G H := by
  unfold vectorPairing pairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, add_mul, cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_add ((hF i).integrable_mul (hH i)) ((hG i).integrable_mul (hH i))

/-- Finite sum version of the same spatial identity. -/
theorem vectorPairing_sum_left (Q : TriadicCube 2) {ι : Type*} (S : Finset ι)
    (F : ι → Vec 2 → Vec 2) (H : Vec 2 → Vec 2)
    (hF : ∀ k, ∀ i, MemLp (fun x => F k x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q (∑ k ∈ S, F k) H = ∑ k ∈ S, vectorPairing Q (F k) H := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [vectorPairing, pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, vectorPairing_add_left Q (hF a)
      (fun i => by simpa only [Finset.sum_apply] using memLp_finsetSum S (fun k _ => hF k i)) hH,
      ih, Finset.sum_insert ha]

/-- The genuine weak gradient of a finite sum of H¹ functions. -/
theorem square_h1_sum_grad (Q : TriadicCube 2) {ι : Type*} (S : Finset ι)
    (u : ι → H1Function (openCubeSet Q)) : (∑ k ∈ S, u k).grad = ∑ k ∈ S, (u k).grad := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, H1Function.zero_grad]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, H1Function.add_grad, ih, Finset.sum_insert ha]
    rfl

/-- The actual finite potential associated with the projection at depth `2N+2`. -/
def squarePartialPotential (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (N : ℕ) :
    H1Function (openCubeSet Q) := ∑ k ∈ Finset.range (N+1), ratioNinePotential Q G k

/-- Its weak equation has exactly the telescoped cell-projected source. -/
theorem squarePartialPotential_pairing (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (N : ℕ)
    (φ : H1Function (openCubeSet Q)) :
    vectorPairing Q (squarePartialPotential Q G N).grad φ.grad =
      vectorPairing Q (squareProjection Q (2*N+2) G) φ.grad := by
  unfold squarePartialPotential
  rw [square_h1_sum_grad,
    vectorPairing_sum_left Q _ _ _ (fun k i => memLp_normalized_of_memL2On
      ((ratioNinePotential Q G k).gradMemL2 i))
      (fun i => memLp_normalized_of_memL2On (φ.gradMemL2 i))]
  have heq (k : ℕ) : vectorPairing Q (ratioNinePotential Q G k).grad φ.grad =
      vectorPairing Q (ratioNineBlock Q G k) φ.grad := squareGradientPotential_pairing Q _ φ
  simp_rw [heq]
  rw [← vectorPairing_sum_left Q _ _ _ (ratioNineBlock_memLp Q G)
    (fun i => memLp_normalized_of_memL2On (φ.gradMemL2 i)), sum_ratioNineBlock]

/-- The gradient residual contracts from the actual cell-projection residual of a gradient. -/
theorem squarePartialPotential_residual_energy (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) (N : ℕ) :
    squareVectorEnergy Q (u - squarePartialPotential Q u.grad N).grad ≤
      squareVectorEnergy Q (fun x => u.grad x - squareProjection Q (2*N+2) u.grad x) := by
  have hu (i : Fin 2) := memLp_normalized_of_memL2On (u.gradMemL2 i)
  apply weak_gradient_projection_energy_le Q
    (G := fun x => u.grad x - squareProjection Q (2*N+2) u.grad x)
    (fun i => (hu i).sub (projection_memLp Q (2*N+2) _ 2))
    (u - squarePartialPotential Q u.grad N)
  intro φ
  rw [H1Function.sub_grad]
  rw [vectorPairing_sub_left Q hu
      (fun i => memLp_normalized_of_memL2On ((squarePartialPotential Q u.grad N).gradMemL2 i))
      (fun i => memLp_normalized_of_memL2On (φ.gradMemL2 i)),
    vectorPairing_sub_left Q (G := squareProjection Q (2*N+2) u.grad) hu
      (fun i => projection_memLp Q (2*N+2) _ 2)
      (fun i => memLp_normalized_of_memL2On (φ.gradMemL2 i)), squarePartialPotential_pairing]

/-- The actual finite gradient potentials converge in Euclidean L² gradient energy. -/
theorem tendsto_squarePartialPotential_residual_energy (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    Tendsto (fun N => squareVectorEnergy Q (u - squarePartialPotential Q u.grad N).grad)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => 2*N+2) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N ≤ 2*N+2; omega) tendsto_id
  exact squeeze_zero (fun _ => squareVectorEnergy_nonneg Q _)
    (squarePartialPotential_residual_energy Q u)
    ((tendsto_squareVectorEnergy_projection_residual Q
      (fun i => memLp_normalized_of_memL2On (u.gradMemL2 i))).comp hi)

end ASDExplicitGamma.Cold
