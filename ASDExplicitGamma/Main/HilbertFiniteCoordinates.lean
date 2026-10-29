module

public import ASDExplicitGamma.Main.HilbertColumnProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite Hilbert coordinate identities for the actual positive Haar norm. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

/-- Euclidean coordinates commute with normalized integrated energy. -/
theorem main_hilbertEnergy_euclidean {κ : Type*} [Fintype κ] (Q : TriadicCube 2)
    {F : Vec 2 → EuclideanSpace ℝ κ} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q F = ∑ i, energy Q (fun x => (F x).ofLp i) := by
  unfold hilbertEnergy
  simp_rw [EuclideanSpace.real_norm_sq_eq, energy_eq_integral_sq]
  apply integral_finsetSum
  intro i _
  let pr : EuclideanSpace ℝ κ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : κ => ℝ) i
  have hi := (pr.comp_memLp' hF).integrable_norm_pow (by norm_num : 2 ≠ 0)
  simpa only [pr, PiLp.proj_apply, Real.norm_eq_abs, sq_abs, Function.comp_apply] using hi

/-- Scalar increments are exactly the coordinates of the Hilbert increment. -/
theorem main_hilbertIncrement_coordinate {κ : Type*} [Fintype κ] (Q : TriadicCube 2)
    {F : Vec 2 → EuclideanSpace ℝ κ} (hF : MemLp F 2 (normalizedCubeMeasure Q)) (j : ℕ) (i : κ) :
    cubeIncrement Q j (fun x => (F x).ofLp i) =
      fun x => (hilbertCubeIncrement Q j F x).ofLp i := by
  rw [← hilbertCubeIncrement_real]
  exact hilbertCubeIncrement_map Q j (PiLp.proj 2 (fun _ : κ => ℝ) i) hF

/-- Every finite coordinate retains genuine positive-Haar series membership. -/
theorem main_hilbert_coordinate_summable {κ : Type*} [Fintype κ] (Q : TriadicCube 2)
    {F : Vec 2 → EuclideanSpace ℝ κ} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F))) (i : κ) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => (F x).ofLp i))) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (energy_nonneg Q _)) _ hP
  intro k
  rw [main_hilbertIncrement_coordinate Q hF, main_hilbertEnergy_euclidean Q (hilbertCubeIncrement_memLp Q (k+1) F)]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum
      (f := fun j : κ => energy Q (fun x => (hilbertCubeIncrement Q (k+1) F x).ofLp j))
      (fun j _ => energy_nonneg Q _) (Finset.mem_univ i)) (by positivity)

/-- The Hilbert primal energy is exactly the sum of coordinate primal energies. -/
theorem main_hilbertPrimalEnergy_euclidean {κ : Type*} [Fintype κ] (Q : TriadicCube 2)
    {F : Vec 2 → EuclideanSpace ℝ κ} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F))) :
    hilbertPrimalEnergy Q (Real.sqrt 3) F =
      ∑ i, primalEnergy Q (Real.sqrt 3) (fun x => (F x).ofLp i) := by
  have he (k : ℕ) : (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F) =
      ∑ i, (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => (F x).ofLp i)) := by
    rw [main_hilbertEnergy_euclidean Q (hilbertCubeIncrement_memLp Q (k+1) F), Finset.mul_sum]
    simp_rw [main_hilbertIncrement_coordinate Q hF]
  simp only [hilbertPrimalEnergy, primalEnergy, he]
  rw [Summable.tsum_finsetSum (fun i _ => main_hilbert_coordinate_summable Q hF hP i), Finset.sum_add_distrib]
  rw [main_hilbertEnergy_euclidean Q (hilbertCubeIncrement_memLp Q 0 F)]
  simp_rw [main_hilbertIncrement_coordinate Q hF]

end ASDExplicitGamma.Main
