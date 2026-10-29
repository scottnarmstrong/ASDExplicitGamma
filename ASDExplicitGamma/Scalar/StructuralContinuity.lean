module

public import ASDExplicitGamma.Scalar.ViscosityAnnealed

/-! Exact structural continuity in the true scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization
open Algsuperdiff.Section3

/-- The exact multiplicative scalar corridor for every natural label increment. -/
theorem sigmaBar_structural_continuity_nat (M : ABKModel 2) (m : ℤ) (j : ℕ) :
    1 ≤ (Annealed.sigmaBar M (m+(j:ℤ)) : ℝ)/(Annealed.sigmaBar M m : ℝ) ∧
    (Annealed.sigmaBar M (m+(j:ℤ)) : ℝ)/(Annealed.sigmaBar M m : ℝ) ≤
      Real.rpow 3 (2*M.gamma*(j:ℝ)) := by
  let c := Real.rpow 3 (M.gamma*(j:ℝ))
  let r := Real.rpow 3 (-(M.gamma*(j:ℝ)))
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg M.shellPrefix.gamma_pos.le (Nat.cast_nonneg j)))
  have hi : c*r=1 := by
    dsimp [c,r]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3),add_neg_cancel,Real.rpow_zero]
  have hir : r⁻¹=c := by
    apply (mul_left_cancel₀ hr.ne')
    rw [mul_inv_cancel₀ hr.ne',mul_comm r c,hi]
  have hb := sigmaBar_viscosity_comparison M r hr hr1 m
  change r*(Annealed.sigmaBar M m : ℝ) ≤ (Annealed.sigmaBar (viscosityShiftModel M (j:ℤ)) m : ℝ) ∧
    (Annealed.sigmaBar (viscosityShiftModel M (j:ℤ)) m : ℝ) ≤ r⁻¹*(Annealed.sigmaBar M m : ℝ) at hb
  have he := sigmaBar_exact_law_nat M m j
  change (Annealed.sigmaBar M (m+(j:ℤ)) : ℝ)=c*(Annealed.sigmaBar (viscosityShiftModel M (j:ℤ)) m : ℝ) at he
  have hl := mul_le_mul_of_nonneg_left hb.1 hc.le
  have hu := mul_le_mul_of_nonneg_left hb.2 hc.le
  rw [← mul_assoc,hi,one_mul,← he] at hl
  rw [← he,hir,← mul_assoc,← pow_two] at hu
  have hc2 : c^2=Real.rpow 3 (2*M.gamma*(j:ℝ)) := by
    dsimp [c]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    push_cast
    ring
  rw [hc2] at hu
  have hs := (Annealed.sigmaBar_characterization M m).1
  constructor
  · exact (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hl)
  · exact (div_le_iff₀ hs).mpr hu

/-- The source integer-label continuity bound, with no small-gamma or numerical premise. -/
theorem sigmaBar_structural_continuity (M : ABKModel 2) (m r : ℤ) (hr : 0 ≤ r) :
    1 ≤ (Annealed.sigmaBar M (m+r) : ℝ)/(Annealed.sigmaBar M m : ℝ) ∧
    (Annealed.sigmaBar M (m+r) : ℝ)/(Annealed.sigmaBar M m : ℝ) ≤ Real.rpow 3 (2*M.gamma*(r:ℝ)) := by
  obtain ⟨j,rfl⟩ := Int.eq_ofNat_of_zero_le hr
  simpa only [Int.cast_natCast] using sigmaBar_structural_continuity_nat M m j

end ASDExplicitGamma.Scalar
