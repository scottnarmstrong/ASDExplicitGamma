module

public import ASDExplicitGamma.Triadic.DiagPeriodGrid
public import ASDExplicitGamma.Triadic.DiagMeshVertices

/-! Exact correspondence of the source reflected neighbors and periodic cells. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators Fin.CommRing

noncomputable section

/-- Periodic cell immediately below a mesh vertex in the chosen bit direction. -/
def diagNodalPeriodIndex {N : ℕ} [NeZero (2*N)] (z : Fin (N+1)) (b : Fin 2) : Fin (2*N) :=
  (z.val : Fin (2*N)) - (b.val : Fin (2*N))

theorem diagNodalPeriodIndex_val {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (z : Fin (N+1)) (b : Fin 2) :
    (diagNodalPeriodIndex z b).val =
      if z.val = 0 ∧ b.val = 1 then 2*N-1 else z.val-b.val := by
  have hz : z.val < 2*N := by have := z.isLt; omega
  have hb : b.val < 2*N := by have := b.isLt; omega
  unfold diagNodalPeriodIndex
  rw [Fin.val_sub, Fin.val_cast_of_lt hz, Fin.val_cast_of_lt hb]
  by_cases h : z.val = 0 ∧ b.val = 1
  · rw [ite_eq_left h, h.1, h.2, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h]
    have hle : b.val ≤ z.val := by have := b.isLt; omega
    have heq : 2*N-b.val+z.val = 2*N+(z.val-b.val) := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]

theorem diagNodalPeriodIndex_sign {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (z : Fin (N+1)) (b : Fin 2) :
    diagReflectSign N (diagNodalPeriodIndex z b) = diagNeighborSign N z b := by
  unfold diagReflectSign diagNeighborSign
  rw [diagNodalPeriodIndex_val hN]
  have hz := z.isLt
  fin_cases b <;> by_cases h0 : z.val = 0 <;> by_cases h1 : z.val = N <;>
    simp_all <;> omega

theorem diagNodalPeriodIndex_fold {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (z : Fin (N+1)) (b : Fin 2) :
    ((diagReflectIndex N (diagNodalPeriodIndex z b)).val : ℝ) = diagNeighborIndex N z b := by
  unfold diagReflectIndex
  simp only [diagNodalPeriodIndex_val hN]
  have hz := z.isLt
  by_cases hz0 : z.val = 0
  · have hlast : ¬2*N-1 < N := by omega
    fin_cases b <;> simp [diagNeighborIndex, hz0, hN, hlast]
  · by_cases hzN : z.val = N
    · have hprev : N-1 < N := by omega
      have hfold : 2*N-1-N = N-1 := by omega
      fin_cases b <;> simp [diagNeighborIndex, hzN, hN.ne', hprev,
        hfold, Nat.cast_sub (show 1 ≤ N by omega)]
    · have hzlt : z.val < N := by omega
      have hzpos : 1 ≤ z.val := by omega
      have hprev : z.val-1 < N := by omega
      fin_cases b <;> simp [diagNeighborIndex, hz0, hzN, hzlt, hprev, Nat.cast_sub hzpos]

end

end ASDExplicitGamma.Triadic
