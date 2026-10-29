module

public import Homogenization.Geometry.TriadicCube
public import ASDExplicitGamma.Inverse.StoppedPlanarGraph
public import ASDExplicitGamma.Gaussian.SupMeanDyadicSquare
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Closed physical carriers of the source two-by-two buffered blocks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

/-- The source physical block side, in ordinary spatial units. -/
def physicalBlockSide (j : ℤ) : ℝ := 2*(3:ℝ)^(j+40)

/-- A side-s collection of physical buffered blocks, with the half-fine-cell
shift dictated by the centered triadic grid. Its closed carrier also contains
all boundary observations of the derivative supremum. -/
def physicalBlockRegion (j : ℤ) (a : BlockSite) (s : ℕ) : Set (Vec 2) :=
  {x | ∀ d, physicalBlockSide j*(a d:ℝ)-(3:ℝ)^j/2 ≤ x d ∧
    x d ≤ physicalBlockSide j*((a d:ℝ)+s)-(3:ℝ)^j/2}

theorem physical_block_side_pos (j : ℤ) : 0 < physicalBlockSide j := by
  unfold physicalBlockSide
  exact mul_pos (by norm_num) (zpow_pos (by norm_num) _)

theorem physical_block_region_measurable (j : ℤ) (a : BlockSite) (s : ℕ) :
    MeasurableSet (physicalBlockRegion j a s) := by
  have hi (d : Fin 2) : MeasurableSet {x : Vec 2 |
      physicalBlockSide j*(a d:ℝ)-(3:ℝ)^j/2 ≤ x d ∧
      x d ≤ physicalBlockSide j*((a d:ℝ)+s)-(3:ℝ)^j/2} :=
    (measurableSet_le measurable_const (measurable_pi_apply d)).inter
      (measurableSet_le (measurable_pi_apply d) measurable_const)
  simpa only [physicalBlockRegion,Set.iInter_ofPred] using MeasurableSet.iInter hi

/-- Two separated coordinate intervals retain the full intervening block gap. -/
theorem physical_interval_gap (W t : ℝ) (hW : 0 ≤ W) (a b : ℤ) (s : ℕ)
    (hgap : 2*(s:ℤ) ≤ |b-a|) (x y : ℝ)
    (hx : W*(a:ℝ)-t ≤ x ∧ x ≤ W*((a:ℝ)+s)-t)
    (hy : W*(b:ℝ)-t ≤ y ∧ y ≤ W*((b:ℝ)+s)-t) :
    W*s ≤ |x-y| := by
  rcases le_total a b with hab | hba
  · have hi : 2*(s:ℤ) ≤ b-a := by simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hgap
    have hr : 2*(s:ℝ) ≤ (b:ℝ)-(a:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_left hr hW
    have hxy : W*s ≤ y-x := by nlinarith only [hx.2,hy.1,hm]
    exact hxy.trans (le_abs_self (y-x)) |>.trans_eq (abs_sub_comm y x)
  · have hi : 2*(s:ℤ) ≤ a-b := by simpa only [abs_of_nonpos (sub_nonpos.mpr hba),neg_sub] using hgap
    have hr : 2*(s:ℝ) ≤ (a:ℝ)-(b:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_left hr hW
    have hxy : W*s ≤ x-y := by nlinarith only [hy.2,hx.1,hm]
    exact hxy.trans (le_abs_self (x-y))

/-- Joint-restriction independence can use these closed carriers: a coordinate
gap of two side-s block populations leaves a physical gap of W*s. -/
theorem physical_block_region_gap (j : ℤ) (a b : BlockSite) (s : ℕ)
    (hgap : ∃ d, 2*(s:ℤ) ≤ |b d-a d|)
    {x y : Vec 2} (hx : x ∈ physicalBlockRegion j a s)
    (hy : y ∈ physicalBlockRegion j b s) :
    ∃ d, physicalBlockSide j*s ≤ |(x-y) d| := by
  obtain ⟨d,hd⟩ := hgap
  exact ⟨d,physical_interval_gap _ _ (physical_block_side_pos j).le _ _ s hd _ _ (hx d) (hy d)⟩

end
end ASDExplicitGamma.Inverse
