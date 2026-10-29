module

public import ASDExplicitGamma.Cold.ResidualAxialProfile

/-! # The constrained square spectral gap, mode by mode -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The exceptional first axial pair. -/
def axialBadSet (i : Fin 2) : Set (Fin 2 → ℤ) :=
  {p | p (Fin.rev i) = 0 ∧ (p i) ^ 2 = 1}

/-- The exceptional pair consists of exactly the two signed first modes. -/
theorem axialBadSet_eq (i : Fin 2) :
    axialBadSet i = {axialFirst i 1, axialFirst i (-1)} := by
  ext p
  constructor
  · intro hp
    have hm : (p i - 1) * (p i + 1) = 0 := by nlinarith only [hp.2]
    rcases mul_eq_zero.mp hm with hn | hn
    · exact Or.inl (axial_eq_first hp.1 (by linarith only [hn]))
    · exact Or.inr (axial_eq_first hp.1 (by linarith only [hn]))
  · rintro (rfl | rfl) <;> fin_cases i <;> norm_num [axialBadSet, axialFirst]

/-- A signed contribution which pays the exceptional pair from higher axial energy. -/
def residualAxialWeight (i : Fin 2) (a : (Fin 2 → ℤ) → ℝ) (p : Fin 2 → ℤ) : ℝ :=
  (axialBadSet i).indicator (fun q => -(a q ^ 2)) p +
    (7 / 9 : ℝ) * (axialHighSet i).indicator (fun q => a q ^ 2) p

/-- The axial weight has the exact convergent sum used in the spectral assembly. -/
theorem residualAxialWeight_hasSum (i : Fin 2) (a : (Fin 2 → ℤ) → ℝ)
    (ha : Summable (fun p => a p ^ 2)) (hneg : a (axialFirst i (-1)) = -a (axialFirst i 1)) :
    HasSum (residualAxialWeight i a)
      (-2 * a (axialFirst i 1) ^ 2 + (7 / 9 : ℝ) *
        ∑' p, (axialHighSet i).indicator (fun q => a q ^ 2) p) := by
  classical
  have hl : HasSum ((axialBadSet i).indicator (fun p => -(a p ^ 2)))
      (-2 * a (axialFirst i 1) ^ 2) := by
    have h := (hasSum_ite_eq (axialFirst i 1) (-(a (axialFirst i 1) ^ 2))).add
      (hasSum_ite_eq (axialFirst i (-1)) (-(a (axialFirst i 1) ^ 2)))
    have hlim : -(a (axialFirst i 1) ^ 2) + -(a (axialFirst i 1) ^ 2) =
        -2 * a (axialFirst i 1) ^ 2 := by ring
    rw [hlim] at h
    apply h.congr_fun
    intro p
    rw [axialBadSet_eq]
    by_cases hp : p = axialFirst i 1
    · subst p; simp [axialFirst_ne i]
    by_cases hn : p = axialFirst i (-1)
    · subst p; simp [Ne.symm (axialFirst_ne i), hneg]
    · simp [hp, hn]
  exact hl.add ((ha.indicator (axialHighSet i)).hasSum.mul_left (7 / 9 : ℝ))

/-- An integer square is either zero, one, or at least four. -/
theorem int_sq_cases_real (n : ℤ) :
    (n : ℝ) ^ 2 = 0 ∨ (n : ℝ) ^ 2 = 1 ∨ 4 ≤ (n : ℝ) ^ 2 := by
  by_cases hn : -1 ≤ n ∧ n ≤ 1
  · have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl | rfl <;> norm_num
  · have hcases : n ≤ -2 ∨ 2 ≤ n := by omega
    right; right
    rcases hcases with h | h
    · have hr : (n : ℝ) ≤ -2 := by exact_mod_cast h
      nlinarith only [hr]
    · have hr : 2 ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith only [hr]

/-- The real algebra at a pair of squared integer frequencies. -/
theorem residual_mode_gap {a b s : ℝ} (hs : 0 ≤ s)
    (ha : a = 0 ∨ a = 1 ∨ 4 ≤ a) (hb : b = 0 ∨ b = 1 ∨ 4 ≤ b)
    (hzero : a = 0 → b = 0 → s = 0) :
    (if b = 0 ∧ a = 1 then -a * s else 0) +
      (if b = 0 ∧ 9 ≤ a then (7 / 9 : ℝ) * a * s else 0) +
      ((if a = 0 ∧ b = 1 then -b * s else 0) +
      (if a = 0 ∧ 9 ≤ b then (7 / 9 : ℝ) * b * s else 0)) ≤ (a + b - 2) * s := by
  rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
  all_goals try (have hz : s = 0 := hzero rfl rfl; rw [hz]; norm_num)
  all_goals split_ifs <;> norm_num at * <;> nlinarith

end ASDExplicitGamma.Cold
