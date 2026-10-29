module

public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpect
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovMajorant
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovXi

/-! MA-E-COVARIANCE, expectation step 5: expectations of the proxy majorants. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem hotCov_err_energy_cellavg_Th (Q : TriadicCube 2) (d : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    oldSignedCellAverage Q d (fun U => ∑' c : BlockCoord 2,
      vecNormSq (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))) =
    descendantsAverage Q d (fun U => hotCovErrCellEnergy Q U b L true) +
    descendantsAverage Q d (fun U => hotCovErrCellEnergy Q U b L false) := by
  rw [← descendantsAverage_add, ← old_signed_cell_average_eq_descendantsAverage]
  congr 1
  funext U
  rw [tsum_fintype, Fintype.sum_sum_type]
  simp [hotCovErrCol, hotCovErrCellEnergy, vecNormSq, vecDot, hotCovPlusC, hotCovIdxC, pow_two]

/-- Expectation of the covariance-error majorant: `E KE2 <= (xi/2)(e_+^2 + e_-^2)`. -/
theorem hotCov_pe_expect_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b B0 : ℝ) (L : {l : ℝ // 0 < l})
    (hL : cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 ≤ L.1)
    (hB : oldSignedFlatBoundaryEnergy (originCube 2 (m + hobs)) b L ≤ B0) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (hotCovPE_Th M m hobs t b L) μ ∧
    (∫ ω, hotCovPE_Th M m hobs t b L ω ∂μ) ≤
      xi / 2 * (mainFlatBoundaryEPlus (b ^ 2) B0 ^ 2 + mainFlatBoundaryEMinus (b ^ 2) B0 ^ 2) := by
  intro μ xi
  have hν : ∀ U : OldSignedCellIndex (originCube 2 (m + hobs)) (hobs + 5),
      Summable (fun c : BlockCoord 2 => vecNormSq
        (hotCovErrCol (originCube 2 (m + hobs)) U.val b L (hotCovPlusC c) (hotCovIdxC c))) :=
    fun U => (hasSum_fintype _).summable
  have pay := hotCov_cellavg_payment_Th (I := BlockCoord 2) M h hM hγ N hpast m hm hobs t ht
    (fun U c => hotCovErrCol (originCube 2 (m + hobs)) U.val b L (hotCovPlusC c) (hotCovIdxC c)) hν
  have hPE : hotCovPE_Th M m hobs t b L = fun ω => oldSignedCellAverage
      (originCube 2 (m + hobs)) (hobs + 5) (fun U => ∑' c : BlockCoord 2,
        oldSignedDirectionalProxy U.val (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U.val ω))
          (hotCovErrCol (originCube 2 (m + hobs)) U.val b L (hotCovPlusC c) (hotCovIdxC c))) := by
    funext ω
    simp only [hotCovPE_Th, hotCovSkewProxy_Th, tsum_fintype]
  rw [hPE]
  refine ⟨pay.1, pay.2.trans ?_⟩
  rw [hotCov_err_energy_cellavg_Th]
  have hcp := hotCov_err_cap_plus (originCube 2 (m + hobs)) (hobs + 5) b B0 L hL hB
  have hcm := hotCov_err_cap_minus (originCube 2 (m + hobs)) (hobs + 5) b B0 L hL hB
  have e1 : descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
      (fun U => hotCovErrCellEnergy (originCube 2 (m + hobs)) U b L true) ≤
      mainFlatBoundaryEPlus (b ^ 2) B0 ^ 2 :=
    (Real.sqrt_le_iff.mp hcp).2
  have e2 : descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
      (fun U => hotCovErrCellEnergy (originCube 2 (m + hobs)) U b L false) ≤
      mainFlatBoundaryEMinus (b ^ 2) B0 ^ 2 :=
    (Real.sqrt_le_iff.mp hcm).2
  have hxi : 0 ≤ xi / 2 := by
    have := hotCov_xi_nonneg_Th M h hγ m t ht
    positivity
  exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) hxi

theorem hotCov_mean_energy_cellavg_Th (Q : TriadicCube 2) (d : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U => ∑' n : whiteBasisIndex,
      vecNormSq (hotCovFlatMeanVec Q b L (hotCovPlusC c) U.val n (hotCovIdxC c))) =
    descendantsAverage Q d (fun U => ∑' n : whiteBasisIndex, ∑ i : Fin 2,
      vecNormSq (hotCovFlatMeanVec Q b L true U n i)) +
    descendantsAverage Q d (fun U => ∑' n : whiteBasisIndex, ∑ i : Fin 2,
      vecNormSq (hotCovFlatMeanVec Q b L false U n i)) := by
  have hs (plus : Bool) (U : OldSignedCellIndex Q d) (i : Fin 2) :=
    hotCov_flat_mean_vec_sq_summable Q d b L plus U.val U.property i
  have hsw (plus : Bool) (U : OldSignedCellIndex Q d) :
      ∑' n : whiteBasisIndex, ∑ i : Fin 2, vecNormSq (hotCovFlatMeanVec Q b L plus U.val n i) =
      ∑ i : Fin 2, ∑' n : whiteBasisIndex, vecNormSq (hotCovFlatMeanVec Q b L plus U.val n i) :=
    Summable.tsum_finsetSum fun i _ => hs plus U i
  have key (plus : Bool) : ∑ i : Fin 2, oldSignedCellAverage Q d (fun U => ∑' n : whiteBasisIndex,
      vecNormSq (hotCovFlatMeanVec Q b L plus U.val n i)) =
      descendantsAverage Q d (fun U => ∑' n : whiteBasisIndex, ∑ i : Fin 2,
        vecNormSq (hotCovFlatMeanVec Q b L plus U n i)) := by
    rw [← old_signed_cell_average_eq_descendantsAverage]
    unfold oldSignedCellAverage
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun U _ => (hsw plus U).symm
  rw [Fintype.sum_sum_type]
  simp only [hotCovPlusC, hotCovIdxC]
  rw [key true, key false]

/-- Expectation of the residual-receiver majorant:
`E Kaff2 <= (xi/2)(2 b^2 + B0/2)`. -/
theorem hotCov_pa_expect_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b B0 : ℝ) (L : {l : ℝ // 0 < l})
    (hB : oldSignedFlatBoundaryEnergy (originCube 2 (m + hobs)) b L ≤ B0) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (fun ω => ∑ c : BlockCoord 2, hotCovPA_Th M m hobs t b L c ω) μ ∧
    (∫ ω, ∑ c : BlockCoord 2, hotCovPA_Th M m hobs t b L c ω ∂μ) ≤
      xi / 2 * (2 * b ^ 2 + B0 / 2) := by
  intro μ xi
  have pay (c : BlockCoord 2) : Integrable (hotCovPA_Th M m hobs t b L c) μ ∧
      (∫ ω, hotCovPA_Th M m hobs t b L c ω ∂μ) ≤ xi / 2 *
        oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
          ∑' n : whiteBasisIndex, vecNormSq (hotCovFlatMeanVec (originCube 2 (m + hobs)) b L
            (hotCovPlusC c) U.val n (hotCovIdxC c))) :=
    hotCov_cellavg_payment_Th (I := whiteBasisIndex)
    M h hM hγ N hpast m hm hobs t ht
    (fun U n => hotCovFlatMeanVec (originCube 2 (m + hobs)) b L (hotCovPlusC c) U.val n
      (hotCovIdxC c))
    (fun U => hotCov_flat_mean_vec_sq_summable _ _ b L (hotCovPlusC c) U.val U.property _)
  have hint := integrable_finset_sum (Finset.univ : Finset (BlockCoord 2))
    (fun c _ => (pay c).1)
  refine ⟨hint, ?_⟩
  rw [integral_finset_sum _ fun c _ => (pay c).1]
  refine (Finset.sum_le_sum fun c _ => (pay c).2).trans ?_
  rw [← Finset.mul_sum, hotCov_mean_energy_cellavg_Th]
  have hxi : 0 ≤ xi / 2 := by
    have := hotCov_xi_nonneg_Th M h hγ m t ht
    positivity
  exact mul_le_mul_of_nonneg_left (hotCov_mean_avg_both_le _ _ b B0 L hB) hxi

end

end ASDExplicitGamma.Main
