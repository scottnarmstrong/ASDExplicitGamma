module

public import ASDExplicitGamma.Native.OldSignedFullPatchProjection
public import ASDExplicitGamma.Native.OldSignedPrimalTraceGap

/-! The physical-flux trace payment after genuine coarse subadditivity. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Parent coarse energy is below the exact child average, by positivity
of the genuine parent-minus-patch comparison energy. -/
theorem old_signed_parent_energy_le_child (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ≤
      descendantsAverage Q depth (fun U => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) P)) := by
  intro a
  have h := old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k
    ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P))
  rw [old_signed_parent_patch_energy] at h
  exact sub_nonneg.mp h

/-- The four-load parent defect is at most its child average, with the
same coefficient and scalar frame on every actual cell. -/
theorem old_signed_parent_trace_le_child (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    traceDefect (openCubeSet Q) a 1 ≤
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  intro a
  have h := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    old_signed_parent_energy_le_child Q depth nu sigma hnu hsigma k (blockBasis c))
  rw [←Homogenization.descendantsAverage_sum] at h
  simp_rw [old_signed_coarse_basis_trace_sum] at h
  simp only [traceDefect,inv_one,one_mul]
  rw [old_signed_descendants_average_sub,descendantsAverage_const]
  exact sub_le_sub_right h 4

end
end ASDExplicitGamma.Native
