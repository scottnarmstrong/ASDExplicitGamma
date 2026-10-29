module

public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! A structural centered-cube descendant lemma exported independently so
depth-specific consumers do not unfold descendant populations. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3
  Algsuperdiff.Section3.Provider.ErrorComparison

/-- For every depth, the centered cube at that depth belongs to the
corresponding descendant population. -/
theorem originCube_mem_descendantsAtDepth' (d : ℕ) (n : ℤ) (j : ℕ) :
    originCube d (n - (j : ℤ)) ∈ descendantsAtDepth (originCube d n) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [descendantsAtDepth_succ]
      refine Finset.mem_biUnion.mpr
        ⟨originCube d (n - (j : ℤ)), ih, ?_⟩
      have h := originCube_pred_mem_childCubes d (n - (j : ℤ))
      have hstep : n - (j : ℤ) - 1 = n - ((j + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [hstep] at h

/-- Offset form of centered membership.  Keeping the offset as an addition
avoids normalizing a large `n - j` expression at the use site. -/
theorem originCube_mem_descendantsAtOffset (d : ℕ) (n : ℤ) (j : ℕ) :
    originCube d n ∈ descendantsAtDepth (originCube d (n + (j : ℤ))) j := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [descendantsAtDepth_succ]
      refine Finset.mem_biUnion.mpr ⟨originCube d (n + 1), ?_, ?_⟩
      · have hroot : n + 1 + (j : ℤ) = n + ((j + 1 : ℕ) : ℤ) := by
          push_cast
          ring
        simpa only [hroot] using ih (n + 1)
      · have h := originCube_pred_mem_childCubes d (n + 1)
        have hstep : n + 1 - 1 = n := by omega
        simpa only [hstep] using h

end ASDExplicitGamma.Inverse
