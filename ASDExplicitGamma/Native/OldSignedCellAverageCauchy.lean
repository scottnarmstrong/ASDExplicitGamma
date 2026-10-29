module

public import ASDExplicitGamma.Native.OldSignedCellAverage
public import Mathlib.Analysis.Real.Sqrt

/-! Exact Cauchy--Schwarz for dependent physical cell profiles. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- Nonnegative actual cell data have a nonnegative spatial average. -/
theorem old_signed_cell_average_nonneg (Q : TriadicCube 2) (r : ℕ)
    (f : OldSignedCellIndex Q r → ℝ) (hf : ∀ U,0≤f U) :
    0≤oldSignedCellAverage Q r f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun U _ => hf U))

/-- Cauchy--Schwarz keeps the physical averaging weights exactly, even when
the profile carries the membership proof of the cell. -/
theorem old_signed_cell_average_cauchy (Q : TriadicCube 2) (r : ℕ)
    (f g : OldSignedCellIndex Q r → ℝ) :
    oldSignedCellAverage Q r (fun U => f U*g U)≤
      Real.sqrt (oldSignedCellAverage Q r (fun U => f U^2))*
        Real.sqrt (oldSignedCellAverage Q r (fun U => g U^2)) := by
  let c := ((descendantsAtDepth Q r).card:ℝ)⁻¹
  have hc : 0≤c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g) hc
  unfold oldSignedCellAverage
  change c*(∑ U,f U*g U)≤Real.sqrt (c*∑ U,f U^2)*Real.sqrt (c*∑ U,g U^2)
  rw [Real.sqrt_mul hc,Real.sqrt_mul hc]
  have he : Real.sqrt c*Real.sqrt (∑ U,f U^2)*(Real.sqrt c*Real.sqrt (∑ U,g U^2))=
      c*(Real.sqrt (∑ U,f U^2)*Real.sqrt (∑ U,g U^2)) := by
    calc
      _ = (Real.sqrt c*Real.sqrt c)*(Real.sqrt (∑ U,f U^2)*Real.sqrt (∑ U,g U^2)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hc]
  rw [he]
  exact hh

/-- Square-root energy profiles contract through their full spatial sums. -/
theorem old_signed_cell_average_root_cauchy (Q : TriadicCube 2) (r : ℕ)
    (f g : OldSignedCellIndex Q r → ℝ) (hf : ∀ U,0≤f U) (hg : ∀ U,0≤g U) :
    oldSignedCellAverage Q r (fun U => Real.sqrt (f U)*Real.sqrt (g U))≤
      Real.sqrt (oldSignedCellAverage Q r f)*Real.sqrt (oldSignedCellAverage Q r g) := by
  have hh := old_signed_cell_average_cauchy Q r (fun U => Real.sqrt (f U)) (fun U => Real.sqrt (g U))
  simpa only [Real.sq_sqrt (hf _),Real.sq_sqrt (hg _)] using hh

/-- The physical descendant average preserves constants exactly. -/
theorem old_signed_cell_average_const (Q : TriadicCube 2) (r : ℕ) (c : ℝ) :
    oldSignedCellAverage Q r (fun _ => c)=c := by
  rw [old_signed_cell_average_eq_descendantsAverage Q r (fun _ => c),descendantsAverage_const]

/-- The spatial first moment is bounded by its root second moment. -/
theorem old_signed_cell_average_le_root (Q : TriadicCube 2) (r : ℕ)
    (f : OldSignedCellIndex Q r → ℝ) :
    oldSignedCellAverage Q r f≤Real.sqrt (oldSignedCellAverage Q r (fun U => f U^2)) := by
  have hh := old_signed_cell_average_cauchy Q r f (fun _ => 1)
  simpa only [mul_one,one_pow,old_signed_cell_average_const,Real.sqrt_one] using hh

end
end ASDExplicitGamma.Native
