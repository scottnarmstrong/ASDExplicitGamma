module

public import ASDExplicitGamma.Inverse.StoppedLocalObservationGeometry

/-! The full doubled localization carriers are separated by the source 7N colors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

/-- Coordinate interval separation with distinct width and intervening margin. -/
theorem physical_interval_gap_with_margin (W t : ℝ) (hW : 0 ≤ W)
    (a b : ℤ) (s gap : ℕ) (hgap : ((s+gap:ℕ):ℤ) ≤ |b-a|) (p r : ℝ)
    (hp : W*(a:ℝ)-t ≤ p ∧ p ≤ W*((a:ℝ)+s)-t)
    (hr : W*(b:ℝ)-t ≤ r ∧ r ≤ W*((b:ℝ)+s)-t) :
    W*gap ≤ |p-r| := by
  rcases le_total a b with hab | hba
  · have hi : ((s+gap:ℕ):ℤ) ≤ b-a := by simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hgap
    have hreal : (s:ℝ)+gap ≤ (b:ℝ)-(a:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_left hreal hW
    have hpr : W*gap ≤ r-p := by nlinarith only [hp.2,hr.1,hm]
    exact hpr.trans (le_abs_self (r-p)) |>.trans_eq (abs_sub_comm r p)
  · have hi : ((s+gap:ℕ):ℤ) ≤ a-b := by simpa only [abs_of_nonpos (sub_nonpos.mpr hba),neg_sub] using hgap
    have hreal : (s:ℝ)+gap ≤ (a:ℝ)-(b:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_left hreal hW
    have hpr : W*gap ≤ p-r := by nlinarith only [hr.2,hp.1,hm]
    exact hpr.trans (le_abs_self (p-r))

/-- A 7N coordinate gap separates all points of both full observation
carriers by the largest retained shell range 3^(j+40+M). -/
theorem localized_physical_regions_separated (j : ℤ) (M : ℕ) (x y : BlockSite)
    (hgap : ∃ d, (7:ℤ)*(3^M:ℤ) ≤ |y d-x d|)
    {p r : Vec 2} (hp : p ∈ localizedPhysicalRegion j M x)
    (hr : r ∈ localizedPhysicalRegion j M y) :
    ∃ d, (3:ℝ)^(j+40+M) ≤ |(p-r) d| := by
  obtain ⟨d,hd⟩ := hgap
  have hN : (1:ℕ) ≤ 3^M := one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)
  have hgap' : (((4*3^M+1)+(3^M):ℕ):ℤ) ≤
      |(y d-2*(3^M:ℤ))-(x d-2*(3^M:ℤ))| := by
    rw [show (y d-2*(3^M:ℤ))-(x d-2*(3^M:ℤ)) = y d-x d by ring]
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    have hN' : (1:ℤ) ≤ 3^M := by exact_mod_cast hN
    omega
  have hg := physical_interval_gap_with_margin (physicalBlockSide j) ((3:ℝ)^j/2)
    (physical_block_side_pos j).le _ _ (4*3^M+1) (3^M) hgap' (p d) (r d) (hp d) (hr d)
  refine ⟨d,?_⟩
  rw [zpow_add₀ (by norm_num : (3:ℝ) ≠ 0),zpow_natCast]
  simp only [physicalBlockSide,Nat.cast_pow,Nat.cast_ofNat] at hg
  have hz : 0 ≤ (3:ℝ)^(j+40)*(3:ℝ)^M := by positivity
  change (3:ℝ)^(j+40)*(3:ℝ)^M ≤ |p d-r d|
  nlinarith only [hg,hz]

end
end ASDExplicitGamma.Inverse
