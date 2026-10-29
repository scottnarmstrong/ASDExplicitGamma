module

public import ASDExplicitGamma.Cold.PlateauTransportLimit
public import ASDExplicitGamma.Cold.PlateauWeightTelescope

/-! # The source plateau weights for two genuine H¹ gradients -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Actual projected vector energies contract. -/
theorem squareProjection_energy_le (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) (r : ℕ) :
    squareVectorEnergy Q (squareProjection Q r G) ≤ squareVectorEnergy Q G :=
  Finset.sum_le_sum fun i _ => energy_projection_le Q r (hG i)

/-- The positive ratio-nine scales used in a finite partial sum. -/
def plateauPositiveScales (N : ℕ) : Finset ℕ := (Finset.range N).image Nat.succ

/-- Their sums have the usual successor indexing. -/
theorem sum_plateauPositiveScales {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ k ∈ plateauPositiveScales N, f k = ∑ n ∈ Finset.range N, f (n+1) := by
  unfold plateauPositiveScales
  exact Finset.sum_image (fun _ _ _ _ h => Nat.succ.inj h)

/-- Every scale in the finite fine set is positive. -/
theorem plateauPositiveScales_pos {N k : ℕ} (hk : k ∈ plateauPositiveScales N) : 1 ≤ k := by
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hk
  omega

/-- The finite potential has exactly the top-plus-fine decomposition used in the assembly. -/
theorem squarePartialPotential_eq_top_add (Q : TriadicCube 2) (G : Vec 2 → Vec 2) (N : ℕ) :
    squarePartialPotential Q G N = ratioNinePotential Q G 0 +
      ∑ k ∈ plateauPositiveScales N, ratioNinePotential Q G k := by
  rw [sum_plateauPositiveScales, squarePartialPotential, Finset.sum_range_succ', add_comm]

/-- The actual two-source fine block energy is the difference of projected energies. -/
theorem plateau_fine_block_energy (Q : TriadicCube 2) {G H : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) (n : ℕ) :
    squareVectorEnergy Q (ratioNineBlock Q G (n+1)) + squareVectorEnergy Q (ratioNineBlock Q H (n+1)) =
      (squareVectorEnergy Q (squareProjection Q (2*(n+2)) G) +
       squareVectorEnergy Q (squareProjection Q (2*(n+2)) H)) -
      (squareVectorEnergy Q (squareProjection Q (2*(n+1)) G) +
       squareVectorEnergy Q (squareProjection Q (2*(n+1)) H)) := by
  rw [ratioNineBlock_energy Q hG (by omega), ratioNineBlock_energy Q hH (by omega),
    show 2*(n+1)+2 = 2*(n+2) by omega]
  ring

/-- CO-PLATEAU-P2 for two actual H¹ gradients, before rotation to a solenoidal flux. -/
theorem plateau_gradient_weights (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q)) :
    |plateauTransport Q u w| ≤ ∑' k : ℕ, plateauEvenWeight k *
      (squareVectorEnergy Q (squareProjection Q (2*(k+1)) u.grad) +
       squareVectorEnergy Q (squareProjection Q (2*(k+1)) w.grad)) := by
  let V : ℕ → ℝ := fun k => squareVectorEnergy Q (squareProjection Q (2*k) u.grad) +
    squareVectorEnergy Q (squareProjection Q (2*k) w.grad)
  let M := squareVectorEnergy Q u.grad + squareVectorEnergy Q w.grad
  have hu (i : Fin 2) := memLp_normalized_of_memL2On (u.gradMemL2 i)
  have hw (i : Fin 2) := memLp_normalized_of_memL2On (w.gradMemL2 i)
  have hV (k : ℕ) : 0 ≤ V k := add_nonneg (squareVectorEnergy_nonneg Q _) (squareVectorEnergy_nonneg Q _)
  have hM (k : ℕ) : V k ≤ M := add_le_add (squareProjection_energy_le Q hu _) (squareProjection_energy_le Q hw _)
  have hf (N : ℕ) :
      2 * |plateauTransport Q (squarePartialPotential Q u.grad N) (squarePartialPotential Q w.grad N)| ≤
        (9 / 4 : ℝ) * V 1 + 7 * ∑ n ∈ Finset.range N,
          (1 / 9 : ℝ) ^ (n+1) * (V (n+2) - V (n+1)) := by
    rw [squarePartialPotential_eq_top_add, squarePartialPotential_eq_top_add]
    have h := plateau_finite_transport_le Q (G := u.grad) (H := w.grad) hu hw (plateauPositiveScales N)
      (fun _ hk => plateauPositiveScales_pos hk)
    simp_rw [sum_plateauPositiveScales] at h ⊢
    simp_rw [plateau_fine_block_energy Q (G := u.grad) (H := w.grad) hu hw] at h
    exact h
  have hleft := (tendsto_plateauTransport_partialPotential Q u w).abs.const_mul 2
  have hright := (tendsto_const_nhds (x := (9 / 4 : ℝ) * V 1)).add
    ((summable_plateau_fine_energy hV hM).hasSum.tendsto_sum_nat.const_mul 7)
  have h := le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hf)
  rw [plateau_energy_telescope hV hM] at h
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp h

end ASDExplicitGamma.Cold
