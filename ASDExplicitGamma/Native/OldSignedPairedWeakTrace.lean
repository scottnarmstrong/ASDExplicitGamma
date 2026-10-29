module

public import ASDExplicitGamma.Native.OldSignedFiniteWeakTraceBound

/-! Complete paired weak-energy bounds for the actual two bottom loads
and for the actual two top loads in the same physical scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- The two pure loads; `true` selects the bottom pair. -/
def oldSignedPairLoad (bottom : Bool) (i : Fin 2) : BlockVec 2 :=
  if bottom then blockBasis (.inr i) else blockBasis (.inl i)

/-- The actual primal and reciprocal defects for a pair of physical loads. -/
def oldSignedPairedDefectField (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (bottom : Bool) : BlockCoord 2 → Vec 2 → Vec 2
  | .inl i => fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k
      (oldSignedPairLoad bottom i) x).1-(oldSignedPairLoad bottom i).1
  | .inr i => fun x => (oldSignedDualReflection Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (oldSignedPairLoad bottom i)) x).1-
        (oldSignedPairLoad (!bottom) i).1

/-- Every actual defect coordinate is square integrable, before the
complete weak series is formed. -/
theorem old_signed_paired_defect_memLp (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (bottom : Bool) (c : BlockCoord 2) (i : Fin 2) :
    MemLp (fun x => oldSignedPairedDefectField Q nu sigma hnu hsigma k bottom c x i) 2
      (normalizedCubeMeasure Q) := by
  cases c with
  | inl j =>
    have hm := (memVectorL2_fst_of_memBlockL2
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (oldSignedPairLoad bottom j)))).sub
      (memVectorL2_const (oldSignedPairLoad bottom j).1)
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hm i)
  | inr j =>
    have hr := old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (oldSignedPairLoad bottom j)))
    have hm := (memVectorL2_fst_of_memBlockL2 hr).sub
      (memVectorL2_const (oldSignedPairLoad (!bottom) j).1)
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hm i)

/-- Each actual load pair, primal and reciprocal together, is bounded by
one complete physical inverse-weighted trace proxy. No estimated premise. -/
theorem old_signed_paired_weak_trace_bound (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) :
    let a := responseFramePlanarCoefficientField nu sigma k
    (∑ c : BlockCoord 2,vectorWeakHaarEnergy Q
      (oldSignedPairedDefectField Q nu sigma hnu hsigma k bottom c)) ≤
      rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  apply old_signed_finite_weak_trace_bound Q a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k)
    _ (old_signed_paired_defect_memLp Q nu sigma hnu hsigma k bottom)
  intro j
  cases bottom
  · have hh := old_signed_top_paired_projection_trace_bound Q j nu sigma hnu hsigma k
    simpa only [oldSignedPairedDefectField,oldSignedPairLoad,Bool.false_eq_true,ite_false,
      Bool.not_false,ite_true,Fintype.sum_sum_type,oldSignedPrimalProjectionEnergy,
      oldSignedReciprocalProjectionEnergy,Finset.sum_add_distrib,Pi.sub_apply,a] using hh
  · have hh := old_signed_bottom_paired_projection_trace_bound Q j nu sigma hnu hsigma k
    simpa only [oldSignedPairedDefectField,oldSignedPairLoad,ite_true,Bool.not_true,
      Bool.false_eq_true,ite_false,Fintype.sum_sum_type,oldSignedPrimalProjectionEnergy,
      oldSignedReciprocalProjectionEnergy,Finset.sum_add_distrib,Pi.sub_apply,a] using hh

end
end ASDExplicitGamma.Native
