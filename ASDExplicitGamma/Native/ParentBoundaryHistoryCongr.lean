module

public import ASDExplicitGamma.Scalar.InverseHistoryBlocks
public import ASDExplicitGamma.Variational.LemmaVH1

/-! Complete inverse histories depend only on descendant reciprocal blocks. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Variational Triadic
noncomputable section

/-- Preserve the entire Haar history under reciprocal-block equality on
all descendants. The physical ellipticity witnesses identify the canonical blocks. -/
theorem parent_boundary_inverse_history_congr_blocks
    (U : TriadicCube 2) (a b : CoeffField 2) (lam Lam lb Lb : ℝ)
    (ha : IsEllipticFieldOn lam Lam (openCubeSet U) a)
    (hb : IsEllipticFieldOn lb Lb (openCubeSet U) b)
    (hblocks : ∀ d : ℕ,∀ W∈descendantsAtDepth U d,
      (coarseBlockMatrix (cubeSet W) a).lowerRight=(coarseBlockMatrix (cubeSet W) b).lowerRight)
    (q : ℝ) : lemmaVInverseHistory U a q=lemmaVInverseHistory U b q := by
  have hd (d : ℕ) : lemmaVInverseDepthMax U a d=lemmaVInverseDepthMax U b d := by
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_congr
    intro W hW
    rw [inverse_history_lowerRight W a (ha.mono (measurableSet_openCubeSet W)
        (openCubeSet_subset_of_mem_descendantsAtDepth hW)),
      inverse_history_lowerRight W b (hb.mono (measurableSet_openCubeSet W)
        (openCubeSet_subset_of_mem_descendantsAtDepth hW)),hblocks d W hW]
  unfold lemmaVInverseHistory
  simp_rw [hd]

end
end ASDExplicitGamma.Native
