module

public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy
public import ASDExplicitGamma.Native.OldSignedCellHistories

/-! Directional histories depend only on the coefficient on the actual cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse
noncomputable section

/-- The directional matrix is unchanged by an off-cell coefficient extension. -/
theorem old_signed_paired_depth_matrix_congr (Q : TriadicCube 2) (j : ℕ)
    (a b : CoeffField 2) (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    oldSignedPairedDepthMatrix Q j a=oldSignedPairedDepthMatrix Q j b := by
  have he : descendantsAverageBlockMat Q j (fun U => coarseBlockMatrix (openCubeSet U) a)=
      descendantsAverageBlockMat Q j (fun U => coarseBlockMatrix (openCubeSet U) b) := by
    apply blockMat_ext <;> ext c d
    all_goals
      dsimp only [descendantsAverageBlockMat,descendantsAverageMat,descendantsAverage]
      congr 1
      apply Finset.sum_congr rfl
      intro U hU
      rw [old_signed_descendant_coarse_congr Q j a b hab U hU]
  unfold oldSignedPairedDepthMatrix
  rw [he]

/-- The complete directional proxy is intrinsic, including its exact
inverse depth maxima and every directional quadratic. -/
theorem old_signed_directional_proxy_congr (Q : TriadicCube 2)
    (a b : CoeffField 2) {lamA LamA lamB LamB : ℝ}
    (ha : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (hb : IsEllipticFieldOn lamB LamB (openCubeSet Q) b)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) (e : Vec 2) :
    oldSignedDirectionalProxy Q a e=oldSignedDirectionalProxy Q b e := by
  unfold oldSignedDirectionalProxy rawWeakTraceProxy
  congr 1
  apply tsum_congr
  intro j
  dsimp only
  rw [old_signed_inverse_depth_congr Q j a b ha hb hab,
    old_signed_paired_depth_matrix_congr Q j a b hab]

end
end ASDExplicitGamma.Native
