module

public import ASDExplicitGamma.Triadic.VectorHaar
public import Homogenization.Book.Ch02.Theorems.CoarseGrainingEstimates
public import Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput
public import Homogenization.CoarseGraining.AdjointSymmetry.SigmaAdjoint

/-! Mean-gradient and negative Haar energy bounds for Lemma V (H1). -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Triadic

noncomputable section

/-- The mean gradient bound with the actual coarse inverse matrix, not a
uniform ellipticity constant. -/
theorem lemmaV_meanGradient_bound {d : ℕ} (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    vecNormSq (fun i => cubeAverage Q (fun x => u.toH1.grad x i)) ≤
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet Q) a) *
        cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
  have hc : cubeCenter Q ∈ openCubeSet Q := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q)
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    { toCoeffField := a
      lam := lam
      Lam := Lam
      lam_pos := (hEll.2 _ hc).1
      lam_le_Lam := (hEll.2 _ hc).2.1
      aeStronglyMeasurable := by
        intro i j
        have h := ((measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i)) j)
        apply (h.aestronglyMeasurable (μ := volume.restrict (openCubeSet Q))).congr
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
      aeElliptic := by
        filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
        exact hEll.2 x hx }
  have h := Book.Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
    (Book.Ch02.cubeDomain Q) b u
  rw [Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse] at h
  dsimp only [Book.Ch02.averageGradient, Book.Ch02.averageVec] at h
  simpa only [Book.Ch02.averageGradient, Book.Ch02.variationEnergyValue,
    Book.Ch02.variationEnergyIntegrand, Book.Ch02.average, Book.Ch02.averageVec,
    scalarVariationEnergyIntegrand, b, Book.Ch02.cubeDomain_coe,
    cubeAverage_eq_integralAverage_openCubeSet, H1Function.averageGradient,
    integralAverage, volumeAverage] using! h

/-- The largest coarse inverse operator norm among the depth-k descendants. -/
def lemmaVInverseDepthMax {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (k : ℕ) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q k) fun R =>
    Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a)

/-- Complete inverse history with geometric Haar discount q⁻¹. -/
def lemmaVInverseHistory {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (q : ℝ) : ℝ :=
  (1 - q⁻¹) * ∑' k, (q⁻¹) ^ k * lemmaVInverseDepthMax Q a k

theorem lemmaVInverseDepthMax_nonneg {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (k : ℕ) : 0 ≤ lemmaVInverseDepthMax Q a k := by
  exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ => Book.Ch02.matrixNorm_nonneg _

theorem lemmaVInverseDepthMax_le_uniform {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (k : ℕ) :
    lemmaVInverseDepthMax Q a k ≤ 4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹ := by
  have hRec :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
      Q a hEll openCubeOriginEllipticRecoveryExistence
  have hData := openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hk : Q.scale - (k : ℤ) ≤ Q.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le k)
  have hdepth : descendantsAtScale Q (Q.scale - (k : ℤ)) = descendantsAtDepth Q k := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simp
  apply le_trans (b := maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (k : ℤ)) a)
  · apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q k)
    intro R hR
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (k : ℤ)) := by rwa [hdepth]
    obtain ⟨_sigma, _sigmaStar, _kappa, hA, _hS, _hK, _hSigma, _hdet⟩ :=
      hData _ hk R hRscale
    have hlower := coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hA
    have hnorm : Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a) ≤
        coarseSigmaStarInvBlockNorm R a := by
      rw [← hlower]
      calc
        Book.Ch02.matrixNorm (coarseBlockMatrix (openCubeSet R) a).lowerRight ≤
            matNorm (coarseBlockMatrix (openCubeSet R) a).lowerRight :=
          Book.Ch02.matrixNorm_le_matNorm _
        _ = coarseSigmaStarInvBlockNorm R a := by
          unfold coarseSigmaStarInvBlockNorm
          rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
    apply hnorm.trans
    unfold maxDescendantSigmaStarInvNormAtScale finsetSsup
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hRscale, rfl⟩
  · exact maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
      Q a hEll hData k

/-- Qualitative ellipticity makes the complete inverse history convergent. -/
theorem lemmaVInverseHistory_summable {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam q : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hq : 1 < q) :
    Summable (fun k => (q⁻¹) ^ k * lemmaVInverseDepthMax Q a k) := by
  have hw : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq.le)
  have hw1 : q⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq)).2 hq
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg hw _) (lemmaVInverseDepthMax_nonneg Q a k))
    (fun k => mul_le_mul_of_nonneg_left (lemmaVInverseDepthMax_le_uniform Q hEll k)
      (pow_nonneg hw _))
    ((summable_geometric_of_lt_one hw hw1).mul_right
      (4 * (Fintype.card (Fin d) : ℝ) * lam⁻¹))

/-- The sum of the coordinate projection energies is the average of the
squared vector means on the descendant cubes. -/
theorem lemmaV_projectionEnergy_eq_meanGradient {d : ℕ} (Q : TriadicCube d)
    (k : ℕ) (v : H1Function (openCubeSet Q)) :
    (∑ i, energy Q (cubeProjection Q k (fun x => v.grad x i))) =
      descendantsAverage Q k (fun R => vecNormSq
        (fun i => cubeAverage R (fun x => v.grad x i))) := by
  simp_rw [← pairing_projection_energy Q k (v.grad_memL2_normalizedCubeMeasure _),
    pairing_projection_right Q k _ (v.grad_memL2_normalizedCubeMeasure _)]
  simp only [descendantsAverage, vecNormSq, vecDot]
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- The level-k projection energy of a harmonic gradient is bounded by the
actual depth-k inverse maximum times its intrinsic energy. -/
theorem lemmaV_projectionEnergy_bound {d : ℕ} (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q)) (k : ℕ) :
    (∑ i, energy Q (cubeProjection Q k (fun x => u.toH1.grad x i))) ≤
      lemmaVInverseDepthMax Q a k * cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
  let instFiniteQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hInt : IntegrableOn (scalarVariationEnergyIntegrand a u) (cubeSet Q) volume :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
      ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy u)
  rw [lemmaV_projectionEnergy_eq_meanGradient,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q k _ hInt]
  have hpoint (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q k) :
      vecNormSq (fun i => cubeAverage R (fun x => u.toH1.grad x i)) ≤
        lemmaVInverseDepthMax Q a k * cubeAverage R (scalarVariationEnergyIntegrand a u) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
    let instFiniteR : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    let uR := u.restrictOfIsEllipticFieldOn (isOpen_openCubeSet Q) (isOpen_openCubeSet R)
      hsub hEllR
    have hm := lemmaV_meanGradient_bound R hEllR uR
    have hE : 0 ≤ cubeAverage R (scalarVariationEnergyIntegrand a u) := by
      rw [cubeAverage_eq_integralAverage_openCubeSet]
      exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (openCubeSet R) a hEllR uR
    apply hm.trans
    apply mul_le_mul_of_nonneg_right _ hE
    unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hR, rfl⟩
  unfold descendantsAverage
  have hn : 0 ≤ ((descendantsAtDepth Q k).card : ℝ)⁻¹ := by positivity
  calc
    ((descendantsAtDepth Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q k, vecNormSq
          (fun i => cubeAverage R (fun x => u.toH1.grad x i)) ≤
        ((descendantsAtDepth Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q k,
            lemmaVInverseDepthMax Q a k * cubeAverage R (scalarVariationEnergyIntegrand a u) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) hn
    _ = _ := by rw [← Finset.mul_sum]; exact mul_left_comm _ _ _

/-- H1 for a harmonic gradient, with the complete inverse history and
constant one. -/
theorem lemmaV_harmonic_weakHaarEnergy_le {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam q : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hq : 1 < q)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    (∑ i, dualEnergy Q q (fun x => u.toH1.grad x i)) ≤
      lemmaVInverseHistory Q a q * cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
  have hw : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq.le)
  have hw1 : 0 ≤ 1 - q⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le)
  have hs (i : Fin d) : Summable (fun k => (q⁻¹) ^ k *
      energy Q (cubeProjection Q k (fun x => u.toH1.grad x i))) :=
    summable_weighted_projections Q hq (u.toH1.grad_memL2_normalizedCubeMeasure i)
  have hsSum : Summable (fun k => ∑ i, (q⁻¹) ^ k *
      energy Q (cubeProjection Q k (fun x => u.toH1.grad x i))) :=
    summable_sum fun i _ => hs i
  have hEq : (∑ i, dualEnergy Q q (fun x => u.toH1.grad x i)) =
      (1 - q⁻¹) * ∑' k, (q⁻¹) ^ k *
        (∑ i, energy Q (cubeProjection Q k (fun x => u.toH1.grad x i))) := by
    simp_rw [dualEnergy_eq Q hq (u.toH1.grad_memL2_normalizedCubeMeasure _)]
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hs i)]
    congr 1
    exact tsum_congr fun k => (Finset.mul_sum _ _ _).symm
  rw [hEq]
  calc
    (1 - q⁻¹) * ∑' k, (q⁻¹) ^ k *
        (∑ i, energy Q (cubeProjection Q k (fun x => u.toH1.grad x i))) ≤
        (1 - q⁻¹) * ∑' k, ((q⁻¹) ^ k * lemmaVInverseDepthMax Q a k) *
          cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
      apply mul_le_mul_of_nonneg_left _ hw1
      have hleft : Summable (fun k => (q⁻¹) ^ k *
          (∑ i, energy Q (cubeProjection Q k (fun x => u.toH1.grad x i)))) := by
        simpa only [Finset.mul_sum] using hsSum
      apply hleft.tsum_le_tsum _
        ((lemmaVInverseHistory_summable Q hEll hq).mul_right _)
      intro k
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (lemmaV_projectionEnergy_bound Q hEll u k) (pow_nonneg hw _)
    _ = _ := by rw [tsum_mul_right]; unfold lemmaVInverseHistory; ring

/-- The coarse inverse is unchanged by adjunction, on every elliptic cube. -/
theorem lemmaV_inverseCoarse_adjoint_eq {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    sigmaStarInvCoarse (openCubeSet Q) (adjointCoeffField a) =
      sigmaStarInvCoarse (openCubeSet Q) a := by
  have hData := openCubeDescendantDeterministicCoarseData_of_recoveryFamily
    (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
      Q a hEll openCubeOriginEllipticRecoveryExistence)
  have hEllAdj := isEllipticFieldOn_adjointCoeffField hEll
  have hDataAdj := openCubeDescendantDeterministicCoarseData_of_recoveryFamily
    (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
      Q (adjointCoeffField a) hEllAdj openCubeOriginEllipticRecoveryExistence)
  obtain ⟨_, _, _, hA, _⟩ := hData Q.scale le_rfl Q (by simp)
  obtain ⟨_, _, _, hAAdj, _⟩ := hDataAdj Q.scale le_rfl Q (by simp)
  exact sigmaStarInvCoarse_adjointCoeffField_eq_of_isCoarseBlockMatrix hA hAAdj

/-- Adjoint invariance at every depth. -/
theorem lemmaVInverseDepthMax_adjoint_eq {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (k : ℕ) :
    lemmaVInverseDepthMax Q (adjointCoeffField a) k = lemmaVInverseDepthMax Q a k := by
  unfold lemmaVInverseDepthMax
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  rw [lemmaV_inverseCoarse_adjoint_eq R
    (hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_of_mem_descendantsAtDepth hR))]

/-- The same complete inverse history serves primal and adjoint solutions. -/
theorem lemmaVInverseHistory_adjoint_eq {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (q : ℝ) :
    lemmaVInverseHistory Q (adjointCoeffField a) q = lemmaVInverseHistory Q a q := by
  simp only [lemmaVInverseHistory, lemmaVInverseDepthMax_adjoint_eq Q hEll]

/-- The order-1/4 vector Haar version of H1 used in Lemma V. -/
theorem lemmaV_harmonic_vectorWeakHaarEnergy_le {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    vectorWeakHaarEnergy Q u.toH1.grad ≤
      lemmaVInverseHistory Q a (Real.sqrt 3) *
        cubeAverage Q (scalarVariationEnergyIntegrand a u) :=
  lemmaV_harmonic_weakHaarEnergy_le Q hEll (by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
    simpa using h) u

/-- H1 for adjoint-harmonic functions, with exactly the primal inverse history. -/
theorem lemmaV_adjoint_vectorWeakHaarEnergy_le {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    vectorWeakHaarEnergy Q u.toH1.grad ≤
      lemmaVInverseHistory Q a (Real.sqrt 3) *
        cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) u) := by
  have h := lemmaV_harmonic_vectorWeakHaarEnergy_le Q
    (isEllipticFieldOn_adjointCoeffField hEll) u
  rwa [lemmaVInverseHistory_adjoint_eq Q hEll] at h

end

end ASDExplicitGamma.Variational
