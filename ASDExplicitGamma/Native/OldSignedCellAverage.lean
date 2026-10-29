module

public import ASDExplicitGamma.Native.OldSignedPartitionSeries

/-! The actual finite cell average for quantities whose coefficient and
projection carry the proof that the cell belongs to the physical partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- The actual descendant cells, with their partition membership. -/
abbrev OldSignedCellIndex (Q : TriadicCube 2) (depth : ℕ) :=
  {U : TriadicCube 2 // U ∈ descendantsAtDepth Q depth}

/-- Equal-volume averaging of the actual cell family. -/
def oldSignedCellAverage (Q : TriadicCube 2) (depth : ℕ)
    (f : OldSignedCellIndex Q depth → ℝ) : ℝ :=
  ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U, f U

/-- Proof-independent data recover the usual descendant average exactly. -/
theorem old_signed_cell_average_eq_descendantsAverage (Q : TriadicCube 2) (depth : ℕ)
    (f : TriadicCube 2 → ℝ) :
    oldSignedCellAverage Q depth (fun U => f U.val)=descendantsAverage Q depth f := by
  unfold oldSignedCellAverage descendantsAverage
  rw [Finset.sum_coe_sort (descendantsAtDepth Q depth) f]

/-- Linearity of the actual finite cell average. -/
theorem old_signed_cell_average_add (Q : TriadicCube 2) (depth : ℕ)
    (f g : OldSignedCellIndex Q depth → ℝ) :
    oldSignedCellAverage Q depth (fun U => f U+g U)=
      oldSignedCellAverage Q depth f+oldSignedCellAverage Q depth g := by
  simp only [oldSignedCellAverage,Finset.sum_add_distrib,mul_add]

/-- Scalar multiplication commutes with the finite cell average. -/
theorem old_signed_cell_average_mul (Q : TriadicCube 2) (depth : ℕ)
    (c : ℝ) (f : OldSignedCellIndex Q depth → ℝ) :
    oldSignedCellAverage Q depth (fun U => c*f U)=c*oldSignedCellAverage Q depth f := by
  simp only [oldSignedCellAverage,← Finset.mul_sum]
  ring

/-- Cellwise bounds retain the physical equal-volume weights. -/
theorem old_signed_cell_average_mono (Q : TriadicCube 2) (depth : ℕ)
    {f g : OldSignedCellIndex Q depth → ℝ} (h : ∀ U,f U≤g U) :
    oldSignedCellAverage Q depth f≤oldSignedCellAverage Q depth g := by
  unfold oldSignedCellAverage
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun U _ => h U)) (by positivity)

/-- Genuine complete-mode sums commute with the dependent physical cell
family. No coefficient is defined outside the actual partition. -/
theorem old_signed_cell_average_series {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → OldSignedCellIndex Q depth → ℝ)
    (hs : ∀ U,Summable (fun n => f n U)) :
    Summable (fun n => oldSignedCellAverage Q depth (f n)) ∧
      (∑' n,oldSignedCellAverage Q depth (f n))=
        oldSignedCellAverage Q depth (fun U => ∑' n,f n U) := by
  have hh := (summable_sum (s := Finset.univ) (fun U _ => hs U)).mul_left
    (((descendantsAtDepth Q depth).card : ℝ)⁻¹)
  refine ⟨hh,?_⟩
  unfold oldSignedCellAverage
  rw [tsum_mul_left,Summable.tsum_finsetSum (fun U _ => hs U)]

/-- A finite physical load sum commutes with the cell average. -/
theorem old_signed_cell_average_sum {J : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (s : Finset J) (f : J → OldSignedCellIndex Q depth → ℝ) :
    oldSignedCellAverage Q depth (fun U => ∑ j ∈ s,f j U)=
      ∑ j ∈ s,oldSignedCellAverage Q depth (f j) := by
  classical
  unfold oldSignedCellAverage
  rw [Finset.sum_comm,Finset.mul_sum]

/-- Subtraction commutes with the actual cell average. -/
theorem old_signed_cell_average_sub (Q : TriadicCube 2) (depth : ℕ)
    (f g : OldSignedCellIndex Q depth → ℝ) :
    oldSignedCellAverage Q depth (fun U => f U-g U)=
      oldSignedCellAverage Q depth f-oldSignedCellAverage Q depth g := by
  simp only [oldSignedCellAverage,Finset.sum_sub_distrib,mul_sub]

/-- Absolute values can be bounded inside the finite physical average. -/
theorem old_signed_cell_average_abs_le (Q : TriadicCube 2) (depth : ℕ)
    (f : OldSignedCellIndex Q depth → ℝ) :
    |oldSignedCellAverage Q depth f|≤oldSignedCellAverage Q depth (fun U => |f U|) := by
  unfold oldSignedCellAverage
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)

end
end ASDExplicitGamma.Native
