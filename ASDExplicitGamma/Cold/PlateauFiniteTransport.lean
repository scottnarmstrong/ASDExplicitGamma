module

public import ASDExplicitGamma.Cold.PlateauFineBlock
public import ASDExplicitGamma.Cold.PlateauFiniteAssembly
public import ASDExplicitGamma.Cold.RatioNineProjection

/-! # Transport of finite sums of the actual projected potentials -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Finite additivity of the actual transport form. -/
theorem plateauTransport_sum_left (Q : TriadicCube 2) {ι : Type*} (S : Finset ι)
    (u : ι → H1Function (openCubeSet Q)) (w : H1Function (openCubeSet Q)) :
    plateauTransport Q (∑ k ∈ S, u k) w = ∑ k ∈ S, plateauTransport Q (u k) w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [plateauTransport, normalizedSquareTransport, squareTransportForm, H1Function.zero_grad]
  | @insert a S ha ih => rw [Finset.sum_insert ha, plateauTransport_add_left, ih, Finset.sum_insert ha]

/-- Finite additivity in the second argument. -/
theorem plateauTransport_sum_right (Q : TriadicCube 2) {ι : Type*} (S : Finset ι)
    (u : H1Function (openCubeSet Q)) (w : ι → H1Function (openCubeSet Q)) :
    plateauTransport Q u (∑ k ∈ S, w k) = ∑ k ∈ S, plateauTransport Q u (w k) := by
  rw [plateauTransport_swap, plateauTransport_sum_left]
  simp_rw [plateauTransport_swap Q _ u]
  rw [Finset.sum_neg_distrib]

/-- Every finite family of actual non-top block potentials satisfies the assembled estimate. -/
theorem plateau_finite_transport_le (Q : TriadicCube 2) {G H : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q))
    (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k) :
    2 * |plateauTransport Q
      (ratioNinePotential Q G 0 + ∑ k ∈ S, ratioNinePotential Q G k)
      (ratioNinePotential Q H 0 + ∑ k ∈ S, ratioNinePotential Q H k)| ≤
      (9 / 4 : ℝ) * (squareVectorEnergy Q (squareProjection Q 2 G) +
        squareVectorEnergy Q (squareProjection Q 2 H)) +
      7 * (∑ k ∈ S, (1 / 9 : ℝ) ^ k *
        (squareVectorEnergy Q (ratioNineBlock Q G k) + squareVectorEnergy Q (ratioNineBlock Q H k))) := by
  let a : ℕ → ℝ := fun k => Real.sqrt (squareVectorEnergy Q (ratioNineBlock Q G k))
  let b : ℕ → ℝ := fun k => Real.sqrt (squareVectorEnergy Q (ratioNineBlock Q H k))
  let t : ℕ → ℕ → ℝ := fun k l =>
    plateauTransport Q (ratioNinePotential Q G k) (ratioNinePotential Q H l)
  have ha (k : ℕ) : 0 ≤ a k := Real.sqrt_nonneg _
  have hb (k : ℕ) : 0 ≤ b k := Real.sqrt_nonneg _
  have hGu (k : ℕ) : Real.sqrt (squareVectorEnergy Q (ratioNinePotential Q G k).grad) ≤ a k :=
    Real.sqrt_le_sqrt (ratioNinePotential_energy_le Q G k)
  have hHw (k : ℕ) : Real.sqrt (squareVectorEnergy Q (ratioNinePotential Q H k).grad) ≤ b k :=
    Real.sqrt_le_sqrt (ratioNinePotential_energy_le Q H k)
  have h00 : |t 0 0| ≤ a 0 ^ 2 + b 0 ^ 2 := by
    have h := (abs_plateauTransport_top_le Q (ratioNinePotential Q G 0) (ratioNinePotential Q H 0)).trans
      (add_le_add (ratioNinePotential_energy_le Q G 0) (ratioNinePotential_energy_le Q H 0))
    simpa only [a, b, Real.sq_sqrt (squareVectorEnergy_nonneg Q _)] using h
  have hf : ∀ k ∈ S, ∀ l ∈ S, |t k l| ≤
      (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ max k l * a k * b l := by
    intro k hk l hl
    exact abs_plateauTransport_fine_pair_le Q k l (ratioNineBlock_memLp Q G k)
      (ratioNineBlock_memLp Q H l)
      (ratioNineBlock_projection_zero Q hG (by have := hS k hk; omega))
      (ratioNineBlock_projection_zero Q hH (by have := hS l hl; omega))
      (ratioNinePotential_primitive Q G k) (ratioNinePotential_primitive Q H l)
      (ratioNinePotential_energy_le Q G k) (ratioNinePotential_energy_le Q H l)
  have h0 : ∀ l ∈ S, |t 0 l| ≤ (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ l * a 0 * b l := by
    intro l hl
    dsimp [t]
    rw [← abs_neg (plateauTransport Q _ _), ← plateauTransport_swap]
    have h := (abs_plateauTransport_fine_left_le Q l (ratioNineBlock_memLp Q H l)
      (ratioNineBlock_projection_zero Q hH (by have := hS l hl; omega))
      (ratioNinePotential_primitive Q H l) (ratioNinePotential Q G 0)).trans
      (mul_le_mul_of_nonneg_left (hGu 0) (by positivity))
    convert h using 1
    ring
  have h1 : ∀ k ∈ S, |t k 0| ≤ (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ k * a k * b 0 := by
    intro k hk
    exact (abs_plateauTransport_fine_left_le Q k (ratioNineBlock_memLp Q G k)
      (ratioNineBlock_projection_zero Q hG (by have := hS k hk; omega))
      (ratioNinePotential_primitive Q G k) (ratioNinePotential Q H 0)).trans
      (mul_le_mul_of_nonneg_left (hHw 0) (by positivity))
  have h := plateau_finite_entry_assembly S hS a b ha hb t h00 h0 h1 hf
  have hexp : plateauTransport Q
      (ratioNinePotential Q G 0 + ∑ k ∈ S, ratioNinePotential Q G k)
      (ratioNinePotential Q H 0 + ∑ k ∈ S, ratioNinePotential Q H k) =
      t 0 0 + (∑ l ∈ S, t 0 l) + (∑ k ∈ S, t k 0) + ∑ k ∈ S, ∑ l ∈ S, t k l := by
    rw [plateauTransport_add_left, plateauTransport_add_right, plateauTransport_add_right]
    simp_rw [plateauTransport_sum_left, plateauTransport_sum_right]
    dsimp [t]
    ring
  rw [hexp]
  convert h using 1
  simp only [a, b, Real.sq_sqrt (squareVectorEnergy_nonneg Q _), ratioNineBlock,
    ↓reduceIte, mul_add, Finset.sum_add_distrib]

end ASDExplicitGamma.Cold
