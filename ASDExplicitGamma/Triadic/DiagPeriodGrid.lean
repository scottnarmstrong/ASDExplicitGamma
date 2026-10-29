module

public import ASDExplicitGamma.Triadic.DiagStencilBounds
public import ASDExplicitGamma.Triadic.DiagSourceRow
public import Mathlib.Data.ZMod.Basic

/-! The doubled planar source period and its exact source energy census. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators Fin.CommRing

noncomputable section

/-- Integer coordinate lags, represented on the doubled source period. -/
def diagPeriodLag (N : ℕ) [NeZero (2*N)] : (ℤ × ℤ) →+ (Fin 2 → Fin (2*N)) where
  toFun g i := if i = 0 then (g.1 : Fin (2*N)) else (g.2 : Fin (2*N))
  map_zero' := by funext i; dsimp; split_ifs <;> exact Int.cast_zero
  map_add' g h := by
    funext i
    dsimp
    split_ifs <;> simp only [Int.cast_add]

/-- The integer unit lag in one planar coordinate. -/
def diagAxisLag (i : Fin 2) : ℤ × ℤ := if i = 0 then (1,0) else (0,1)

/-- Odd reflection through each parent face, at the level of actual cell means. -/
def diagOddGrid (N : ℕ) (m : (Fin 2 → Fin N) → ℝ) (k : Fin 2 → Fin (2*N)) : ℝ :=
  diagReflectSign N (k 0) * diagReflectSign N (k 1) * m (fun i => diagReflectIndex N (k i))

theorem diagPeriodShift_eq_add_one {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (k : Fin (2*N)) : diagPeriodShift N k = k + 1 := by
  apply Fin.ext
  rw [diagPeriodShift_val, Fin.val_add_eq_ite, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2*N)]
  have hk := k.isLt
  split_ifs <;> omega

theorem diagPeriodLag_line {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (i : Fin 2) (b t : Fin (2*N)) :
    diagMeshLine i b t + diagPeriodLag N (diagAxisLag i) =
      diagMeshLine i b (diagPeriodShift N t) := by
  rw [diagPeriodShift_eq_add_one hN]
  funext a
  fin_cases i <;> fin_cases a <;> simp [diagMeshLine, diagPeriodLag, diagAxisLag]

theorem diagOddGrid_line {N : ℕ} (m : (Fin 2 → Fin N) → ℝ)
    (i : Fin 2) (b t : Fin (2*N)) :
    diagOddGrid N m (diagMeshLine i b t) =
      diagReflectSign N b * diagReflectOdd N
        (fun a => m (diagMeshLine i (diagReflectIndex N b) a)) t := by
  have hfold : (fun a => diagReflectIndex N (diagMeshLine i b t a)) =
      diagMeshLine i (diagReflectIndex N b) (diagReflectIndex N t) := by
    funext a
    by_cases ha : a = i <;> simp only [diagMeshLine, ha, ite_true, ite_false]
  have hsign : diagReflectSign N (diagMeshLine i b t 0) *
      diagReflectSign N (diagMeshLine i b t 1) = diagReflectSign N b * diagReflectSign N t := by
    fin_cases i <;> simp [diagMeshLine, mul_comm]
  unfold diagOddGrid diagReflectOdd
  rw [hfold, hsign]
  ring

/-- The full planar difference sum is twice the original transverse-row sum. -/
theorem diagOddGrid_difference_sum {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (m : (Fin 2 → Fin N) → ℝ) (i : Fin 2) (r : ℝ) :
    (∑ k : Fin 2 → Fin (2*N),
      ((diagOddGrid N m (k + diagPeriodLag N (diagAxisLag i)) - diagOddGrid N m k) / r)^2) =
    2 * ∑ b : Fin N, ∑ t : Fin (2*N),
      ((diagReflectOdd N (fun a => m (diagMeshLine i b a)) (diagPeriodShift N t) -
        diagReflectOdd N (fun a => m (diagMeshLine i b a)) t) / r)^2 := by
  rw [← diagGridLine_sum i (diagOtherCoordinate i) (diagOtherCoordinate_ne i)]
  simp_rw [diagPeriodLag_line hN, diagOddGrid_line]
  have hpoint (b : Fin (2*N)) (x y : ℝ) :
      ((diagReflectSign N b*x-diagReflectSign N b*y)/r)^2 = ((x-y)/r)^2 := by
    rw [← mul_sub, mul_div_assoc, mul_pow, diagReflectSign_sq, one_mul]
  simp_rw [hpoint]
  let F (b : Fin N) := ∑ t : Fin (2*N),
    ((diagReflectOdd N (fun a => m (diagMeshLine i b a)) (diagPeriodShift N t) -
      diagReflectOdd N (fun a => m (diagMeshLine i b a)) t) / r)^2
  change (∑ b, diagReflectEven N F b) = 2 * ∑ b, F b
  exact diagReflectEven_sum N F

/-- The normalized full-period discrete energy is controlled by the actual
source broken weak energy with constant one. -/
theorem diagSourceGrid_difference_energy (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    ((N : ℝ)⁻¹)^2 / 4 * ∑ i : Fin 2, ∑ k : Fin 2 → Fin (2*N),
      ((diagOddGrid N (diagSourceMeans Q j u.toH1Function)
        (k + diagPeriodLag N (diagAxisLag i)) -
        diagOddGrid N (diagSourceMeans Q j u.toH1Function) k) / diagMeshRadius Q j)^2 ≤
      ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  intro N instPeriodNonzero
  have hN : 0 < N := pow_pos (by norm_num) j
  simp_rw [diagOddGrid_difference_sum hN]
  rw [← Finset.mul_sum]
  have hsource := diagSourceRow_total_energy Q j u
  convert hsource using 1
  ring

end

end ASDExplicitGamma.Triadic
