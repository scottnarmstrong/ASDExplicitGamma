module

public import ASDExplicitGamma.Triadic.DiagSmoothHat

/-! Exact real-space tent kernels underlying the two-cell face identity. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

/-- Away from its three corners, the tent and weak slope are precisely
the two source-cell affine kernels. -/
theorem diagTentKernel_split {r t : ℝ} (hr : 0 < r)
    (h0 : t ≠ 0) (hu : t ≠ r) :
    (diagHat (t / r) = (if -r < t ∧ t < 0 then (t + r) / r else 0) +
      (if 0 < t ∧ t < r then (r - t) / r else 0)) ∧
    (diagHatSlope r t = (if -r < t ∧ t < 0 then 1 / r else 0) +
      (if 0 < t ∧ t < r then -1 / r else 0)) := by
  rcases lt_or_gt_of_ne h0 with ht | ht
  · have hnotpos : ¬0 < t := not_lt.mpr ht.le
    have hnotr : ¬r < t := by linarith only [hr, ht]
    by_cases hleft : -r < t
    · have hsL : -r < t ∧ t < 0 := ⟨hleft, ht⟩
      have hsR : ¬(0 < t ∧ t < r) := fun h => hnotpos h.1
      simp only [hsL, hsR, and_self, ite_true, ite_false, add_zero]
      constructor
      · rw [diagHat_left ⟨(le_div_iff₀ hr).2 (by linarith only [hleft]),
          div_nonpos_of_nonpos_of_nonneg ht.le hr.le⟩]
        field_simp [hr.ne']
        ring
      · simp only [diagHatSlope, hleft, hnotpos, hnotr, ite_true, ite_false]
        ring
    · have hsL : ¬(-r < t ∧ t < 0) := fun h => hleft h.1
      have hsR : ¬(0 < t ∧ t < r) := fun h => hnotpos h.1
      simp only [hsL, hsR, ite_false, add_zero]
      constructor
      · apply diagHat_eq_zero
        rw [abs_div, abs_of_pos hr]
        apply (le_div_iff₀ hr).2
        have h' : r ≤ -t := by linarith only [hleft]
        simpa only [one_mul] using h'.trans (neg_le_abs t)
      · simp only [diagHatSlope, hleft, hnotpos, hnotr, ite_false]
        ring
  · have hpos : 0 < t := ht
    have hleft : -r < t := by linarith only [hr, ht]
    have hnotneg : ¬t < 0 := not_lt.mpr ht.le
    by_cases hright : t < r
    · have hnotr : ¬r < t := not_lt.mpr hright.le
      have hsL : ¬(-r < t ∧ t < 0) := fun h => hnotneg h.2
      have hsR : 0 < t ∧ t < r := ⟨ht, hright⟩
      simp only [hsL, hsR, and_self, ite_true, ite_false, zero_add]
      constructor
      · rw [(diagHat_on_unit ⟨div_nonneg ht.le hr.le, (div_le_one hr).2 hright.le⟩).1]
        field_simp [hr.ne']
      · simp only [diagHatSlope, hleft, hpos, hnotr, ite_true, ite_false]
        ring
    · have hgt : r < t := lt_of_le_of_ne (not_lt.mp hright) hu.symm
      have hsL : ¬(-r < t ∧ t < 0) := fun h => hnotneg h.2
      have hsR : ¬(0 < t ∧ t < r) := fun h => hright h.2
      simp only [hsL, hsR, ite_false, add_zero]
      constructor
      · apply diagHat_eq_zero
        rw [abs_of_pos (div_pos ht hr)]
        exact (one_le_div hr).2 hgt.le
      · simp only [diagHatSlope, hleft, hpos, hgt, ite_true]
        ring

end

end ASDExplicitGamma.Triadic
