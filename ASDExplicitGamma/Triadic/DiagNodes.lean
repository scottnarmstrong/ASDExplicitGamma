module

public import ASDExplicitGamma.Triadic.DiagLinear
import Mathlib.Tactic.FinCases

/-! The four neighboring cell means, with the source odd reflection at faces. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators

noncomputable section

/-- Index of the actual cell supplying one reflected neighbor at a mesh vertex.
The bit `b` selects the cell to the right (`0`) or left (`1`). -/
def diagNeighborIndex (N : ℕ) (z : Fin (N + 1)) (b : Fin 2) : ℝ :=
  if z.val = 0 then 0 else if z.val = N then N - 1 else (z.val : ℝ) - b.val

/-- Odd reflection reverses the sign of the exterior cell at either face. -/
def diagNeighborSign (N : ℕ) (z : Fin (N + 1)) (b : Fin 2) : ℝ :=
  if z.val = 0 then (if b.val = 0 then 1 else -1)
  else if z.val = N then (if b.val = 0 then -1 else 1) else 1

/-- Physical center of a reflected neighboring cell. -/
def diagNeighborCenter (a : Vec 2) (r : ℝ) (N : ℕ)
    (z : Fin 2 → Fin (N + 1)) (b : Fin 2 → Fin 2) : Vec 2 :=
  fun i => a i + (diagNeighborIndex N (z i) (b i) + 1 / 2) * r

/-- The exact four-cell nodal average on the one-cell reflected collar. -/
def diagOddNodalMean (a : Vec 2) (r : ℝ) (N : ℕ)
    (g : Vec 2 → ℝ) (z : Fin 2 → Fin (N + 1)) : ℝ :=
  (∑ b₀ : Fin 2, ∑ b₁ : Fin 2,
    diagNeighborSign N (z 0) b₀ * diagNeighborSign N (z 1) b₁ *
      g (diagNeighborCenter a r N z ![b₀, b₁])) / 4

/-- Odd-reflected neighbors cancel at both faces in the first coordinate. -/
theorem diagOddNodalMean_face0 (a : Vec 2) (r : ℝ) {N : ℕ} (hN : 0 < N)
    (g : Vec 2 → ℝ) (z : Fin 2 → Fin (N + 1))
    (hz : (z 0).val = 0 ∨ (z 0).val = N) :
    diagOddNodalMean a r N g z = 0 := by
  rcases hz with hz | hz
  · have hs0 : diagNeighborSign N (z 0) 0 = 1 := by
      simp [diagNeighborSign, hz]
    have hs1 : diagNeighborSign N (z 0) 1 = -1 := by
      simp [diagNeighborSign, hz]
    have h (b : Fin 2) : diagNeighborCenter a r N z ![0, b] =
        diagNeighborCenter a r N z ![1, b] := by
      funext i
      fin_cases i <;> simp [diagNeighborCenter, diagNeighborIndex, hz]
    simp only [diagOddNodalMean, Fin.sum_univ_two, hs0, hs1]
    rw [h 0, h 1]
    ring
  · have hs0 : diagNeighborSign N (z 0) 0 = -1 := by
      simp [diagNeighborSign, hz, Nat.ne_of_gt hN]
    have hs1 : diagNeighborSign N (z 0) 1 = 1 := by
      simp [diagNeighborSign, hz, Nat.ne_of_gt hN]
    have h (b : Fin 2) : diagNeighborCenter a r N z ![0, b] =
        diagNeighborCenter a r N z ![1, b] := by
      funext i
      fin_cases i <;> simp [diagNeighborCenter, diagNeighborIndex, hz]
    simp only [diagOddNodalMean, Fin.sum_univ_two, hs0, hs1]
    rw [h 0, h 1]
    ring

/-- The same cancellation on the two faces in the second coordinate. -/
theorem diagOddNodalMean_face1 (a : Vec 2) (r : ℝ) {N : ℕ} (hN : 0 < N)
    (g : Vec 2 → ℝ) (z : Fin 2 → Fin (N + 1))
    (hz : (z 1).val = 0 ∨ (z 1).val = N) :
    diagOddNodalMean a r N g z = 0 := by
  rcases hz with hz | hz
  · have hs0 : diagNeighborSign N (z 1) 0 = 1 := by
      simp [diagNeighborSign, hz]
    have hs1 : diagNeighborSign N (z 1) 1 = -1 := by
      simp [diagNeighborSign, hz]
    have h (b : Fin 2) : diagNeighborCenter a r N z ![b, 0] =
        diagNeighborCenter a r N z ![b, 1] := by
      funext i
      fin_cases i <;> simp [diagNeighborCenter, diagNeighborIndex, hz]
    simp only [diagOddNodalMean, Fin.sum_univ_two, hs0, hs1]
    rw [h 0, h 1]
    ring
  · have hs0 : diagNeighborSign N (z 1) 0 = -1 := by
      simp [diagNeighborSign, hz, Nat.ne_of_gt hN]
    have hs1 : diagNeighborSign N (z 1) 1 = 1 := by
      simp [diagNeighborSign, hz, Nat.ne_of_gt hN]
    have h (b : Fin 2) : diagNeighborCenter a r N z ![b, 0] =
        diagNeighborCenter a r N z ![b, 1] := by
      funext i
      fin_cases i <;> simp [diagNeighborCenter, diagNeighborIndex, hz]
    simp only [diagOddNodalMean, Fin.sum_univ_two, hs0, hs1]
    rw [h 0, h 1]
    ring

/-- The reflected nodal average is linear in the field of cell means. -/
def diagOddNodalMeanLinear (a : Vec 2) (r : ℝ) (N : ℕ)
    (z : Fin 2 → Fin (N + 1)) : (Vec 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun g := diagOddNodalMean a r N g z
  map_add' g h := by
    simp only [diagOddNodalMean, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
  map_smul' c g := by
    simp only [diagOddNodalMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc, ← Finset.mul_sum]
    ring

end

end ASDExplicitGamma.Triadic
