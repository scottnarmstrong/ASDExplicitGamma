module

public import ASDExplicitGamma.Native.OldSignedDirectionalDepthTraceBound
public import ASDExplicitGamma.Native.OldSignedFiniteWeakTraceBound

/-! Complete primal/reciprocal weak energy for a fixed directional load. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- The directional counterpart of the complete OLD trace proxy. -/
def oldSignedDirectionalProxy (Q : TriadicCube 2) (a : CoeffField 2) (e : Vec 2) : ℝ :=
  rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
    (fun j => vecDot e (matVecMul (oldSignedPairedDepthMatrix Q j a) e))

/-- Complete directional proxy convergence follows from the genuine trace
proxy and directional trace domination. -/
theorem old_signed_directional_proxy_summable (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax Q a j*
      vecDot e (matVecMul (oldSignedPairedDepthMatrix Q j a) e)) := by
  intro a
  have hs := (old_signed_weak_trace_proxy_summable Q a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k)).mul_right (vecNormSq e)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (lemmaVInverseDepthMax_nonneg Q a j))
      (old_signed_paired_depth_quadratic_nonneg Q j nu sigma hnu hsigma k e)
  · intro j
    exact (mul_le_mul_of_nonneg_left
      (old_signed_directional_depth_trace_bound Q j nu sigma hnu hsigma k e)
      (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
        (lemmaVInverseDepthMax_nonneg Q a j))).trans_eq (by ring)

/-- The directional proxy is nonnegative and bounded by the complete trace
proxy times the squared load, with both series already convergent. -/
theorem old_signed_directional_proxy_nonneg_le (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    0 ≤ oldSignedDirectionalProxy Q a e ∧
      oldSignedDirectionalProxy Q a e ≤ rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1))*vecNormSq e := by
  intro a
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hs := old_signed_directional_proxy_summable Q nu sigma hnu hsigma k e
  have ht := (old_signed_weak_trace_proxy_summable Q a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k)).mul_right (vecNormSq e)
  constructor
  · exact mul_nonneg hc (tsum_nonneg (fun j =>
      mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
        (lemmaVInverseDepthMax_nonneg Q a j))
        (old_signed_paired_depth_quadratic_nonneg Q j nu sigma hnu hsigma k e)))
  · have hh := hs.tsum_le_tsum (fun j =>
      (mul_le_mul_of_nonneg_left
        (old_signed_directional_depth_trace_bound Q j nu sigma hnu hsigma k e)
        (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
          (lemmaVInverseDepthMax_nonneg Q a j))).trans_eq (by ring)) ht
    have hm := mul_le_mul_of_nonneg_left hh hc
    rw [tsum_mul_right] at hm
    exact hm.trans_eq (by unfold rawWeakTraceProxy; ring)

/-- The two physical directional defects share a single complete inverse
proxy. The ordinary and complementary parent energies cancel before summing. -/
theorem old_signed_bottom_directional_weak_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,e)
    let J := oldSignedDualReflection Q nu sigma k S
    vectorWeakHaarEnergy Q (fun x => (S x).1)+
      vectorWeakHaarEnergy Q (fun x => (J x).1-e) ≤
      oldSignedDirectionalProxy Q (responseFramePlanarCoefficientField nu sigma k) e := by
  intro S J
  have hS := memVectorL2_fst_of_memBlockL2 (Lp.memLp S)
  have hJ := (memVectorL2_fst_of_memBlockL2
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (Lp.memLp S))).sub (memVectorL2_const e)
  have hp := old_signed_vector_weak_projection_series Q (fun x => (S x).1)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hS i))
  have hr := old_signed_vector_weak_projection_series Q (fun x => (J x).1-e)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hJ i))
  rw [hp.2,hr.2,←mul_add,←hp.1.tsum_add hr.1]
  unfold oldSignedDirectionalProxy rawWeakTraceProxy
  apply mul_le_mul_of_nonneg_left _
    (sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le))
  apply (hp.1.add hr.1).tsum_le_tsum _
    (old_signed_directional_proxy_summable Q nu sigma hnu hsigma k e)
  intro j
  have hh := mul_le_mul_of_nonneg_left
    (old_signed_bottom_directional_depth_bound Q j nu sigma hnu hsigma k e)
    (pow_nonneg inverse_history_discount_range.1.le (2*j))
  simpa only [oldSignedPrimalProjectionEnergy,oldSignedReciprocalProjectionEnergy,
    Prod.fst_zero,Pi.zero_apply,sub_zero,Pi.sub_apply,mul_add,mul_assoc,S,J] using hh

end
end ASDExplicitGamma.Native
