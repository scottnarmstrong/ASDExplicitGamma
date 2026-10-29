module

public import ASDExplicitGamma.Native.OldSignedPairingPartition
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Complete-mode sums commute with the actual finite normalized spatial
partition after convergence has been supplied on every physical cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory
noncomputable section

/-- Exact passage of a genuinely summable mode family through the
actual descendant average, retaining every cell's old-medium factors. -/
theorem old_signed_partition_series {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → TriadicCube 2 → ℝ)
    (hs : ∀ U ∈ descendantsAtDepth Q depth,Summable (fun n => f n U)) :
    Summable (fun n => descendantsAverage Q depth (f n)) ∧
      (∑' n,descendantsAverage Q depth (f n))=
        descendantsAverage Q depth (fun U => ∑' n,f n U) := by
  have hh := (summable_sum hs).mul_left (((descendantsAtDepth Q depth).card : ℝ)⁻¹)
  refine ⟨hh,?_⟩
  unfold descendantsAverage
  rw [tsum_mul_left,Summable.tsum_finsetSum hs]

end
end ASDExplicitGamma.Native
