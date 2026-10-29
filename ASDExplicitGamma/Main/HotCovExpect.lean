module

public import ASDExplicitGamma.Main.HotCovProxy
public import ASDExplicitGamma.Main.HotCovPathwise
public import ASDExplicitGamma.Main.HotObsVl2

/-! MA-E-COVARIANCE, expectation step 2: cell-averaged proxy payments and the pathwise
domination of `KE2` and `Kaff2` by integrable proxy majorants. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The observer-root restricted coefficient of the hot trial. -/
def hotCovObsCoef (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet (originCube 2 (m + hobs))) :=
  mainAffineOpenResponseRestriction (originCube 2 (m + hobs))
    (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 (m + hobs)))) m t ω)

/-- Cell-averaged proxy payment for deterministic per-cell vector families. -/
theorem hotCov_cellavg_payment {I : Type*} [Countable I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ν : OldSignedCellIndex (originCube 2 (m + hobs)) (hobs + 5) → I → Vec 2)
    (hν : ∀ U, Summable (fun i => vecNormSq (ν U i))) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma mainSourceInversePrefix (theta M) t
    Integrable (fun ω => oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
      ∑' i, oldSignedDirectionalProxy U.val (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U.val ω)) (ν U i))) μ ∧
    (∫ ω, oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
      ∑' i, oldSignedDirectionalProxy U.val (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U.val ω)) (ν U i)) ∂μ) ≤
      xi / 2 * oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
        ∑' i, vecNormSq (ν U i)) := by
  intro μ xi
  have hU (U : OldSignedCellIndex (originCube 2 (m + hobs)) (hobs + 5)) :=
    hotCov_proxy_payment M h hM hγ N hpast m hm t ht U.val
      (hot_obs_cell_scale m hobs U.val U.property) (ν U) (hν U)
  unfold oldSignedCellAverage
  refine ⟨(integrable_finset_sum _ fun U _ => (hU U).1).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finset_sum _ fun U _ => (hU U).1]
  have key : ∑ U : OldSignedCellIndex (originCube 2 (m + hobs)) (hobs + 5), ∫ ω,
      ∑' i, oldSignedDirectionalProxy U.val (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U.val ω)) (ν U i) ∂μ ≤
      xi / 2 * ∑ U : OldSignedCellIndex (originCube 2 (m + hobs)) (hobs + 5),
        ∑' i, vecNormSq (ν U i) :=
    (Finset.sum_le_sum fun U _ => (hU U).2).trans (le_of_eq (by rw [Finset.mul_sum]))
  refine le_trans (mul_le_mul_of_nonneg_left key (by positivity)) (le_of_eq ?_)
  ring

/-- Receiver weak size is paid by the directional proxy of the cell frame. -/
theorem hotCov_rcvC_weak_le (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (c : BlockCoord 2) (U : OldSignedCellIndex Q d)
    (ν : Vec 2) :
    vectorWeakHaarEnergy U.val (hotCovRcvC Q d nu sigma hnu hsigma k c U ν) ≤
      oldSignedDirectionalProxy U.val (responseFramePlanarCoefficientField nu sigma
        (hotCovCellCoef Q d k U)) ν := by
  rcases c with i | i
  · exact hotCov_topRcv_weak_le Q d nu sigma hnu hsigma k U ν
  · exact hotCov_botRcv_weak_le Q d nu sigma hnu hsigma k U ν

/-- The proxy of a deterministic square-summable family is summable. -/
theorem hotCov_proxy_family_summable {I : Type*} (U : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma) (k : ResponseCoefficient (openCubeSet U))
    (ν : I → Vec 2) (hν : Summable (fun i => vecNormSq (ν i))) :
    Summable (fun i => oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField nu sigma k) (ν i)) := by
  have hbound := old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma k
  set C := ASDExplicitGamma.Inverse.rawWeakTraceProxy (lemmaVInverseDepthMax U
    (responseFramePlanarCoefficientField nu sigma k))
    (fun j => descendantsAverage U j (fun V => traceDefect (openCubeSet V)
      (responseFramePlanarCoefficientField nu sigma k) 1)) with hC
  refine (hν.mul_left C).of_nonneg_of_le (fun i => (hbound (ν i)).1) (fun i => ?_)
  simpa [mul_comm] using (hbound (ν i)).2

end

end ASDExplicitGamma.Main
