module

public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace
public import ASDExplicitGamma.Native.OldSignedPrimalTraceGap
public import ASDExplicitGamma.Native.OldSignedErrorProfiles

/-! Actual parent V and G budgets from the paired weak comparison,
with the same physical fields as in the signed generator error ledger. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- The physical primal profile is the sum of its four complete energies. -/
theorem old_signed_primal_error_size_sq (Q U : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2=
      ∑ c : BlockCoord 2,vectorWeakHaarEnergy U (fun x =>
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x).1-(blockBasis c).1) := by
  rw [oldSignedPrimalErrorSize,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp_rw [vectorWeakHaarNorm,Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]

/-- The physical reciprocal profile is the sum of its four complete energies. -/
theorem old_signed_reciprocal_error_size_sq (Q U : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k^2=
      ∑ c : BlockCoord 2,vectorWeakHaarEnergy U (fun x =>
        (oldSignedDualReflection Q nu sigma k
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c)) x).1-(blockBasis c).2) := by
  rw [oldSignedReciprocalErrorSize,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp_rw [vectorWeakHaarNorm,Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
  rfl

/-- The actual four-load primal and reciprocal profiles jointly cost two
trace proxies. This keeps their correlation until after the paired sum. -/
theorem old_signed_parent_paired_weak_bound (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalErrorSize Q Q nu sigma hnu hsigma k^2+
      oldSignedReciprocalErrorSize Q Q nu sigma hnu hsigma k^2 ≤
      2*rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  have hh := add_le_add (old_signed_paired_weak_trace_bound Q nu sigma hnu hsigma k false)
    (old_signed_paired_weak_trace_bound Q nu sigma hnu hsigma k true)
  rw [old_signed_primal_error_size_sq,old_signed_reciprocal_error_size_sq]
  simp only [Fintype.sum_sum_type,oldSignedPairedDefectField,oldSignedPairLoad,
    Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,blockBasis] at hh ⊢
  convert hh using 1 <;> ring

end
end ASDExplicitGamma.Native
