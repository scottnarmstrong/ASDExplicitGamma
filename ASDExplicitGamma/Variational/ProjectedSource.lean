module

public import ASDExplicitGamma.Variational.CompatibleCoercivity
public import ASDExplicitGamma.Scalar.ProjectionFields
public import ASDExplicitGamma.Triadic.PlanarDirichletBridge
public import ASDExplicitGamma.Variational.LocalizedBlockSpace
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Subadditivity

/-! The actual A-orthogonal projection of a pure flux source onto compatible fields. -/

@[expose] public section
namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

/-- The actual pure-second L² load used by the projected-source estimate. -/
def projectedSourceLoad (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) : HilbertBlockL2 (openCubeSet Q) :=
  hilbertPureSecondL2 (openCubeSet Q)
    (toHilbertVectorL2OfVecField (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF))

/-- The A-orthogonal residual of the pure-flux load, in the actual weighted
energy realization on the source cell. -/
noncomputable def projectedSourceField (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → Vec 2} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    BlockL2 (openCubeSet Q) :=
  scalarResidualField Q ν σ hν hσ k (projectedSourceLoad Q hF)

/-- The complementary coefficient reflection of the projected source. -/
noncomputable def projectedSourceCompatibleState (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → Vec 2} (hF : MemLp F 2 (normalizedCubeMeasure Q)) : BlockState 2 :=
  let Z := projectedSourceField Q ν σ hν hσ k hF
  pairedReflectState (responseFramePlanarCoefficientField ν σ k)
    ⟨fun x => (Z x).1, fun x => (Z x).2⟩

private theorem integral_eq_zero_of_volumeAverage_eq_zero {U : Set (Vec 2)}
    {f : Vec 2 → ℝ} (hvol : (volume U).toReal ≠ 0)
    (h : volumeAverage U f = 0) : ∫ x in U, f x ∂volume = 0 := by
  unfold volumeAverage at h
  rcases mul_eq_zero.mp h with hz | hz
  · exact False.elim ((inv_ne_zero hvol) hz)
  · exact hz

theorem lemmaVInverseDepthMax_le_succ (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (k : ℕ) :
    lemmaVInverseDepthMax Q a k ≤ lemmaVInverseDepthMax Q a (k + 1) := by
  let hRec :=
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
      Q a hEll openCubeOriginEllipticRecoveryExistence
  let hData := openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q k) :
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a) ≤
        lemmaVInverseDepthMax Q a (k + 1) := by
    have hscaleR : R.scale = Q.scale - (k : ℤ) :=
      scale_eq_sub_of_mem_descendantsAtDepth hR
    have hkR : R.scale ≤ Q.scale := by rw [hscaleR]; omega
    have hdepthR : Int.toNat (Q.scale - R.scale) = k := by
      rw [hscaleR]
      simp
    have hRscale : R ∈ descendantsAtScale Q R.scale := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hkR, hdepthR]
      exact hR
    obtain ⟨_, _, _, _, hSR, hKR, hSigmaR, hdetR⟩ := hData R.scale hkR R hRscale
    have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
      hEll.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hDesc : ∀ S ∈ descendantsAtDepth R 1,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det := by
      intro S hS
      have hSglobal : S ∈ descendantsAtDepth Q (k + 1) := by
        apply mem_descendantsAtDepth_succ_iff.mpr
        exact ⟨R, hR, by simpa using hS⟩
      have hscaleS : S.scale = Q.scale - ((k + 1 : ℕ) : ℤ) :=
        scale_eq_sub_of_mem_descendantsAtDepth hSglobal
      have hkS : S.scale ≤ Q.scale := by rw [hscaleS]; omega
      have hdepthS : Int.toNat (Q.scale - S.scale) = k + 1 := by
        rw [hscaleS]
        simp
      have hSscale : S ∈ descendantsAtScale Q S.scale := by
        rw [descendantsAtScale_eq_descendantsAtDepth Q hkS, hdepthS]
        exact hSglobal
      exact hData S.scale hkS S hSscale
    have hsub :=
      sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
        1 R a hEllR hSR hKR hSigmaR hdetR hDesc
    have hParentPSD : (sigmaStarInvCoarse (openCubeSet R) a).PosSemidef :=
      sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := openCubeSet R) (a := a) hSR
    have hAvgPSD :
        (descendantsAverageMat R 1 (fun S => sigmaStarInvCoarse (openCubeSet S) a)).PosSemidef := by
      apply descendantsAverageMat_posSemidef
      intro S hS
      obtain ⟨_, _, _, _, hSS, _, _, _⟩ := hDesc S hS
      exact sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse
        (U := openCubeSet S) (a := a) hSS
    have hnorm := Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
      hParentPSD hAvgPSD hsub
    have hnormAvg :=
      Book.Ch02.matrixNorm_descendantsAverageMat_le_finsetSupReal_matrixNorm R 1
        (fun S => sigmaStarInvCoarse (openCubeSet S) a)
    have hchildren : Book.Ch02.finsetSupReal (descendantsAtDepth R 1)
        (fun S => Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet S) a)) ≤
        lemmaVInverseDepthMax Q a (k + 1) := by
      apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty R 1)
      intro S hS
      have hSglobal : S ∈ descendantsAtDepth Q (k + 1) := by
        apply mem_descendantsAtDepth_succ_iff.mpr
        exact ⟨R, hR, by simpa using hS⟩
      unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
      exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨S, hSglobal, rfl⟩
    exact hnorm.trans (hnormAvg.trans hchildren)
  unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q k)
  intro R hR
  exact hpoint R hR

theorem lemmaVInverseHistory_le_of_inverse_discount
    (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam q₁ q₂ : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hq₁ : 1 < q₁) (hq₂ : 1 < q₂) (hInv : q₁⁻¹ ≤ q₂⁻¹) :
    lemmaVInverseHistory Q a q₁ ≤ lemmaVInverseHistory Q a q₂ := by
  let M : ℕ → ℝ := lemmaVInverseDepthMax Q a
  have hMnonneg (k : ℕ) : 0 ≤ M k := lemmaVInverseDepthMax_nonneg Q a k
  have hMmono (k : ℕ) : M k ≤ M (k + 1) := by
    exact lemmaVInverseDepthMax_le_succ Q hEll k
  have hr₁ : 0 ≤ q₁⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq₁.le)
  have hr₂ : 0 ≤ q₂⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq₂.le)
  have hr₁one : q₁⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq₁)).2 hq₁
  have hr₂one : q₂⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq₂)).2 hq₂
  have hC : ∀ k, M k ≤ 8 * lam⁻¹ := by
    intro k
    calc
      M k = lemmaVInverseDepthMax Q a k := rfl
      _ ≤ 4 * 2 * lam⁻¹ := lemmaVInverseDepthMax_le_uniform Q hEll k
      _ = 8 * lam⁻¹ := by ring
  have hCnonneg : 0 ≤ 8 * lam⁻¹ := by
    have hc := hEll.2 (cubeCenter Q) (by
      rw [← ball_cubeCenter_eq_openCubeSet]
      exact Metric.mem_ball_self (cubeRadius_pos Q))
    have hlam : 0 < lam := hc.1
    positivity
  have hsumM (r : ℝ) (hr : 0 ≤ r) (hrone : r < 1) :
      Summable (fun k : ℕ => r ^ k * M k) := by
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg hr _) (hMnonneg k))
      (fun k => mul_le_mul_of_nonneg_left (hC k) (pow_nonneg hr _))
      ((summable_geometric_of_lt_one hr hrone).mul_right (8 * lam⁻¹))
  have hsumD (r : ℝ) (hr : 0 ≤ r) (hrone : r < 1) :
      Summable (fun k : ℕ => r ^ (k + 1) * (M (k + 1) - M k)) := by
    have hs := (summable_geometric_of_lt_one hr hrone).mul_right (8 * lam⁻¹)
    exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg hr _) (sub_nonneg.mpr (hMmono k)))
      (fun k => by
        have hd : M (k + 1) - M k ≤ M (k + 1) := sub_le_self _ (hMnonneg k)
        have hmul : r * M (k + 1) ≤ 1 * (8 * lam⁻¹) :=
          mul_le_mul hrone.le (hC (k + 1)) (hMnonneg (k + 1)) (by norm_num)
        calc
          r ^ (k + 1) * (M (k + 1) - M k) ≤ r ^ (k + 1) * M (k + 1) :=
            mul_le_mul_of_nonneg_left hd (pow_nonneg hr _)
          _ = r ^ k * (r * M (k + 1)) := by rw [pow_succ]; ring
          _ ≤ r ^ k * (8 * lam⁻¹) := by
            simpa using mul_le_mul_of_nonneg_left hmul (pow_nonneg hr k)) hs
  have hAbel (r : ℝ) (hr : 0 ≤ r) (hrone : r < 1) :
      (1 - r) * (∑' k, r ^ k * M k) =
        M 0 + ∑' k, r ^ (k + 1) * (M (k + 1) - M k) := by
    have hsM := hsumM r hr hrone
    have hsD := hsumD r hr hrone
    have hsShift : Summable (fun k : ℕ => r ^ (k + 1) * M (k + 1)) := by
      exact Summable.of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg hr _) (hMnonneg (k + 1)))
        (fun k => by
          have hmul : r * M (k + 1) ≤ 1 * (8 * lam⁻¹) :=
            mul_le_mul hrone.le (hC (k + 1)) (hMnonneg (k + 1)) (by norm_num)
          calc
            r ^ (k + 1) * M (k + 1) = r ^ k * (r * M (k + 1)) := by rw [pow_succ]; ring
            _ ≤ r ^ k * (8 * lam⁻¹) := by
              simpa using mul_le_mul_of_nonneg_left hmul (pow_nonneg hr k))
        ((summable_geometric_of_lt_one hr hrone).mul_right (8 * lam⁻¹))
    have hsTail : Summable (fun k : ℕ => r ^ (k + 1) * M k) := by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hsM.mul_left r
    have hShiftEq : (∑' k, r ^ (k + 1) * M (k + 1)) =
        (∑' k, r ^ k * M k) - M 0 := by
      have hzeroadd : M 0 + (∑' k, r ^ (k + 1) * M (k + 1)) =
          ∑' k, r ^ k * M k := by
        simpa only [pow_zero, one_mul] using hsM.tsum_eq_zero_add.symm
      linarith
    have hDiff : (∑' k, r ^ (k + 1) * (M (k + 1) - M k)) =
        (∑' k, r ^ (k + 1) * M (k + 1)) -
          (∑' k, r ^ (k + 1) * M k) := by
      rw [← hsShift.tsum_sub hsTail]
      apply tsum_congr
      intro k
      ring
    have hTailEq : (∑' k, r ^ (k + 1) * M k) =
        r * (∑' k, r ^ k * M k) := by
      calc
        _ = ∑' k, r * (r ^ k * M k) := by
          apply tsum_congr
          intro k
          rw [pow_succ]
          ring
        _ = _ := tsum_mul_left
    rw [hDiff, hShiftEq]
    rw [hTailEq]
    ring
  have habel₁ := hAbel q₁⁻¹ hr₁ hr₁one
  have habel₂ := hAbel q₂⁻¹ hr₂ hr₂one
  have hterm (k : ℕ) :
      q₁⁻¹ ^ (k + 1) * (M (k + 1) - M k) ≤
        q₂⁻¹ ^ (k + 1) * (M (k + 1) - M k) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr₁ hInv (k + 1))
      (sub_nonneg.mpr (hMmono k))
  have htsum :=
    (hsumD q₁⁻¹ hr₁ hr₁one).tsum_le_tsum hterm (hsumD q₂⁻¹ hr₂ hr₂one)
  unfold lemmaVInverseHistory
  rw [habel₁, habel₂]
  simpa [add_comm] using add_le_add_left htsum (M 0)

/-- The projected source has the source-compatible potential/solenoidal
structure, obtained from the exact correction-space orthogonality. -/
theorem projectedSourceCompatibleState_compatible (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    ScalarCompatible (openCubeSet Q)
      (projectedSourceCompatibleState Q ν σ hν hσ k hF).eval := by
  let U := openCubeSet Q
  letI projectedSourceCompatibilityFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let a := responseFramePlanarCoefficientField ν σ k
  let Z := projectedSourceField Q ν σ hν hσ k hF
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  let Y := pairedReflectState a W
  have hWeval : W.eval = fun x => Z x := by
    funext x
    exact Prod.ext rfl rfl
  have hZ : MemBlockL2 U W.eval := by
    rw [hWeval]
    exact Lp.memLp Z
  have hEll : IsEllipticFieldOn (ν / σ)
      (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U a :=
    responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      ν σ hν hσ k
  have hYmem : MemBlockL2 U Y.eval := compatibleReflectState_memBlockL2 hEll W hZ
  have hvol : (volume U).toReal ≠ 0 := by
    exact (ne_of_gt (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q))
  have hpot : IsPotentialOn U Y.potential :=
    IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_openCubeSet Q))
      (memVectorL2_fst_of_memBlockL2 hYmem) (by
    intro g hg hsol
    let T : Vec 2 → BlockVec 2 := fun x => (0, g x)
    have hT : ScalarVariation U T := by
      refine ⟨memBlockL2_blockField (MemLp.zero) hg, ?_, hsol⟩
      exact isPotentialZeroTraceOn_zero
    have horth0 := scalar_residual_field_orthogonal Q ν σ hν hσ k
      (projectedSourceLoad Q hF) T hT
    have horth : volumeAverage U (fun x => blockVecDot (T x)
        (blockMatVecMul (blockCoeffField a x) (Z x))) = 0 := by
      simpa [U, a, Z, projectedSourceField] using horth0
    have hpoint : (fun x => blockVecDot (T x)
        (blockMatVecMul (blockCoeffField a x) (Z x))) =
        fun x => vecDot (g x) (Y.potential x) := by
      funext x
      change vecDot (0 : Vec 2) ((blockMatVecMul (blockCoeffField a x) (Z x)).1) +
        vecDot (g x) ((blockMatVecMul (blockCoeffField a x) (Z x)).2) =
          vecDot (g x) ((blockMatVecMul (blockCoeffField a x) (Z x)).2)
      simp [vecDot]
    rw [hpoint] at horth
    exact integral_eq_zero_of_volumeAverage_eq_zero hvol horth)
  have hsol : IsSolenoidalOn U Y.flux := by
    intro φ
    let T : Vec 2 → BlockVec 2 := fun x => (φ.toH1Function.grad x, 0)
    have hT : ScalarVariation U T := by
      refine ⟨memBlockL2_blockField φ.toH1Function.grad_memVectorL2 MemLp.zero,
        ?_, isSolenoidalZeroNormalTraceOn_zero⟩
      exact ⟨φ, rfl⟩
    have horth0 := scalar_residual_field_orthogonal Q ν σ hν hσ k
      (projectedSourceLoad Q hF) T hT
    have horth : volumeAverage U (fun x => blockVecDot (T x)
        (blockMatVecMul (blockCoeffField a x) (Z x))) = 0 := by
      simpa [U, a, Z, projectedSourceField] using horth0
    have hpoint : (fun x => blockVecDot (T x)
        (blockMatVecMul (blockCoeffField a x) (Z x))) =
        fun x => vecDot (Y.flux x) (φ.toH1Function.grad x) := by
      funext x
      change vecDot (φ.toH1Function.grad x)
          ((blockMatVecMul (blockCoeffField a x) (Z x)).1) +
        vecDot (0 : Vec 2) ((blockMatVecMul (blockCoeffField a x) (Z x)).2) =
          vecDot ((blockMatVecMul (blockCoeffField a x) (Z x)).1)
            (φ.toH1Function.grad x)
      rw [vecDot_comm]
      simp [vecDot]
    rw [hpoint] at horth
    exact integral_eq_zero_of_volumeAverage_eq_zero hvol horth
  refine ⟨?_, hpot, hsol⟩
  simpa [projectedSourceCompatibleState, Y, W, Z, BlockState.eval] using hYmem

private theorem projectedSourceLoad_eq_components (Q : TriadicCube 2)
    {F : Vec 2 → Vec 2} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    projectedSourceLoad Q hF =
      toHilbertBlockL2OfComponents (MemLp.zero : MemVectorL2 (openCubeSet Q) 0)
        (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF) := by
  let U := openCubeSet Q
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hzero : MemVectorL2 U (0 : Vec 2 → Vec 2) := MemLp.zero
  have hblock : hilbertBlockL2ToBlockL2 (projectedSourceLoad Q hF) =
      toBlockL2OfComponents hzero hFvec := by
    apply Lp.ext
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (F := projectedSourceLoad Q hF),
      (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
        (L := hilbertPureSecond.toContinuousLinearMap)
        (f := toHilbertVectorL2OfVecField hFvec)),
      coeFn_toHilbertVectorL2OfVecField hFvec,
      coeFn_toBlockL2OfComponents hzero hFvec] with x htransport hpure hvec hcomponents
    rw [htransport, hcomponents]
    change (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) x).toBlockVec = _
    have hpure' : hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) x =
        hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField F x) := by
      simpa [hilbertPureSecondL2, hvec] using hpure
    rw [hpure']
    simp [hilbertPureSecond, blockField, HilbertBlockVec.toBlockVec, hilbertifyVecField]
  apply (continuousLinearEquivBlockL2 (U := U)).symm.injective
  calc
    hilbertBlockL2ToBlockL2 (projectedSourceLoad Q hF) =
        toBlockL2OfComponents hzero hFvec := hblock
    _ = hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfComponents hzero hFvec) := by
      symm
      exact PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
        (U := U) hzero hFvec

/-- The projected energy is its literal source pairing with the compatible
potential, before applying Haar duality. -/
theorem projectedSource_energy_eq_pairing (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) =
      vectorPairing Q F
        (fun x => (projectedSourceCompatibleState Q ν σ hν hσ k hF).potential x) := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let Z := projectedSourceField Q ν σ hν hσ k hF
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  let Y := pairedReflectState a W
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hzero : MemVectorL2 U (0 : Vec 2 → Vec 2) := MemLp.zero
  let L : Vec 2 → BlockVec 2 := fun x => (0, F x)
  have hL : MemBlockL2 U L := memBlockL2_blockField hzero hFvec
  have hZ : MemBlockL2 U (fun x => Z x) := Lp.memLp Z
  have hZeq : toHilbertBlockL2OfBlockField hZ =
      scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF) := by
    change toHilbertBlockL2OfBlockField
      (Lp.memLp (hilbertBlockL2ToBlockL2
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)))) = _
    exact hilbert_field_rebuild _
  have hLeq : toHilbertBlockL2OfBlockField hL = projectedSourceLoad Q hF := by
    change toHilbertBlockL2OfComponents hzero hFvec = projectedSourceLoad Q hF
    exact (projectedSourceLoad_eq_components Q hF).symm
  have hbilL := scalar_frame_bilinear_field Q ν σ hν hσ k hZ hL
  rw [hZeq, hLeq] at hbilL
  have hproj := scalar_projection_residual_energy_pairing Q ν σ hν hσ k
    (projectedSourceLoad Q hF)
  have hpair :
      (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) =
      volumeAverage U (fun x => blockVecDot (L x)
        (blockMatVecMul (blockCoeffField a x) (Z x))) := by
    calc
      _ = (scalarFrameRealization Q ν σ hν hσ k).energyBilin
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
          (projectedSourceLoad Q hF) := hproj.symm
      _ = _ := hbilL
  have hpoint : (fun x => blockVecDot (L x)
      (blockMatVecMul (blockCoeffField a x) (Z x))) =
      fun x => vecDot (F x) (Y.potential x) := by
    funext x
    have hstate : W.eval x = Z x := by
      exact Prod.eta _
    calc
      blockVecDot (L x) (blockMatVecMul (blockCoeffField a x) (Z x)) =
          vecDot (F x) (blockMatVecMul (blockCoeffField a x) (Z x)).2 := by
        simp [L, blockVecDot, vecDot]
      _ = vecDot (F x) (Y.potential x) := by
        congr 1
  rw [hpoint] at hpair
  have hYmem := (projectedSourceCompatibleState_compatible Q ν σ hν hσ k hF).1
  have hYpot : MemVectorL2 U Y.potential :=
    memVectorL2_fst_of_memBlockL2 (by simpa [Y, BlockState.eval] using hYmem)
  have hInt (i : Fin 2) : IntegrableOn (fun x => F x i * Y.potential x i) U :=
    (memScalarL2_coord_of_memVectorL2 hFvec i).integrable_mul
      (memScalarL2_coord_of_memVectorL2 hYpot i)
  have hsum : volumeAverage U (fun x => vecDot (F x) (Y.potential x)) =
      vectorPairing Q F Y.potential := by
    unfold vectorPairing
    change volumeAverage U (fun x => ∑ i, F x i * Y.potential x i) = _
    have hInt' : ∀ i ∈ Finset.univ,
        IntegrableOn (fun x => F x i * Y.potential x i) U := by
      intro i hi
      exact hInt i
    rw [volumeAverage_sum Finset.univ (fun i x => F x i * Y.potential x i) hInt']
    apply Finset.sum_congr rfl
    intro i hi
    unfold pairing
    rw [cubeAverage_eq_integralAverage_openCubeSet Q]
    rfl
  exact hpair.trans hsum

/-- The actual A-orthogonal pure-flux projection has the constant-one source
energy estimate.  The source history uses the order-1/8 history; its comparison
with the compatible order-1/4 history follows from subadditivity of the inverse
coarse blocks. -/
theorem projected_source_energy_le_source_history (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i : Fin 2, Summable (fun j : ℕ =>
      (Real.sqrt 3) ^ (j + 1) * energy Q (cubeIncrement Q (j + 1) (fun x => F x i)))) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ≤
      lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) * vectorPositiveHaarEnergy Q F := by
  let U := openCubeSet Q
  letI projectedSourceEnergyFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let a := responseFramePlanarCoefficientField ν σ k
  let Z := projectedSourceField Q ν σ hν hσ k hF
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  let Y := pairedReflectState a W
  let D := scalarFrameRealization Q ν σ hν hσ k
  let E := D.energyBilin
    (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
    (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
  let P := vectorPositiveHaarEnergy Q F
  let C := vectorWeakHaarEnergy Q (fun x i => Y.potential x i)
  change E ≤ lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) * P
  have hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hFcoord : ∀ i : Fin 2,
      MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hCompat := projectedSourceCompatibleState_compatible Q ν σ hν hσ k hF
  have hYmem : MemBlockL2 U Y.eval := by
    simpa [Y, Z, projectedSourceCompatibleState, projectedSourceField, W, a, U,
      BlockState.eval] using hCompat.1
  have hYpot : IsBlockPotentialOn U Y := by
    change IsPotentialOn U (fun x => (Y.eval x).1)
    simpa [Y, Z, projectedSourceCompatibleState, projectedSourceField, W, a, U,
      BlockState.eval] using hCompat.2.1
  have hYsol : IsBlockSolenoidalOn U Y := by
    change IsSolenoidalOn U (fun x => (Y.eval x).2)
    simpa [Y, Z, projectedSourceCompatibleState, projectedSourceField, W, a, U,
      BlockState.eval] using hCompat.2.2
  have hYvec : MemVectorL2 U Y.potential := memVectorL2_fst_of_memBlockL2 hYmem
  have hYcoord : ∀ i : Fin 2,
      MemLp (fun x => Y.potential x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hYvec i)
  have hWeval : W.eval = fun x => Z x := by
    funext x
    exact Prod.eta _
  have hZmem : MemBlockL2 U (fun x => Z x) := Lp.memLp Z
  have hZeq : toHilbertBlockL2OfBlockField hZmem =
      scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF) := by
    change toHilbertBlockL2OfBlockField
      (Lp.memLp (hilbertBlockL2ToBlockL2
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)))) = _
    exact hilbert_field_rebuild _
  have hbilZ := scalar_frame_bilinear_field Q ν σ hν hσ k hZmem hZmem
  rw [hZeq] at hbilZ
  have hblockE : blockPairingAverage U a W W = E := by
    change volumeAverage U (fun x => blockVecDot (W.eval x)
      (blockMatVecMul (blockCoeffField a x) (W.eval x))) = _
    rw [hWeval]
    exact hbilZ.symm
  have hreflectE : blockPairingAverage U a Y Y = blockPairingAverage U a W W := by
    simpa [Y] using pairedReflect_pairingAverage_isometry
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        ν σ hν hσ k) W W
  have hYenergy : blockPairingAverage U a Y Y = E := hreflectE.trans hblockE
  have hE_nonneg : 0 ≤ E := by
    let D0 := scalarFrameEnergyData Q ν σ hν hσ k
    let R0 := scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)
    have hnorm : ‖responseEnergyUp D0 R0‖ ^ 2 = D0.energy R0 R0 := by
      rw [energyCarrier_norm_sq, responseEnergyUp_down]
    have hEeq : E = ‖responseEnergyUp D0 R0‖ ^ 2 := by
      dsimp [E, D, D0, scalarFrameEnergyData, responseEnergyHilbertData]
      exact hnorm.symm
    rw [hEeq]
    positivity
  have hP_nonneg : 0 ≤ P := vectorPositiveHaarEnergy_nonneg Q F
  have hC_nonneg : 0 ≤ C := vectorWeakHaarEnergy_nonneg Q _
  have hpair := projectedSource_energy_eq_pairing Q ν σ hν hσ k hF
  have hpairY : E = vectorPairing Q F (fun x => Y.potential x) := by
    simpa [E, Y, Z, projectedSourceCompatibleState, projectedSourceField, W, a, U] using hpair
  have hdual := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q hFcoord hYcoord hFpos
  rw [← hpairY] at hdual
  have hsqrtP : vectorPositiveHaarNorm Q F = Real.sqrt P := rfl
  have hsqrtC : vectorWeakHaarNorm Q (fun x i => Y.potential x i) = Real.sqrt C := rfl
  rw [hsqrtP, hsqrtC] at hdual
  have hdualSq : E ^ 2 ≤ P * C := by
    have habs : |E| = E := abs_of_nonneg hE_nonneg
    have hsqrtProd : (Real.sqrt P * Real.sqrt C) ^ 2 = P * C := by
      rw [mul_pow, Real.sq_sqrt hP_nonneg, Real.sq_sqrt hC_nonneg]
    nlinarith [hdual]
  have hEll : IsEllipticFieldOn
      (ν / σ) (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U a := by
    simpa [a, U] using responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hcoercive := compatible_coercivity hEll Y hYpot hYsol hYmem
  have hhist : lemmaVInverseHistory Q a (Real.sqrt 3) ≤
      lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    have hq₁ : 1 < Real.sqrt 3 := by
      have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    have hq₂ : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have hqcomp : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 3 := by
      calc
        (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
    have hInv : (Real.sqrt 3)⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hqcomp
    exact lemmaVInverseHistory_le_of_inverse_discount Q hEll hq₁ hq₂ hInv
  have hweak : C ≤ lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) * E := by
    have hcoercive' : C ≤ lemmaVInverseHistory Q a (Real.sqrt 3) * E := by
      rw [hYenergy] at hcoercive
      simpa [C, compatibleInverseHistory, a] using hcoercive
    exact hcoercive'.trans (mul_le_mul_of_nonneg_right hhist hE_nonneg)
  have hPE : E ^ 2 ≤ P *
      (lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) * E) :=
    hdualSq.trans (mul_le_mul_of_nonneg_left hweak hP_nonneg)
  have hB_nonneg : 0 ≤ lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    unfold lemmaVInverseHistory
    apply mul_nonneg
    · have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le)
    · apply tsum_nonneg
      intro j
      exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (by positivity)) j)
        (lemmaVInverseDepthMax_nonneg Q a j)
  by_cases hEzero : E = 0
  · simpa [E, hEzero] using mul_nonneg hB_nonneg hP_nonneg
  · have hEpos : 0 < E := lt_of_le_of_ne hE_nonneg (Ne.symm hEzero)
    have hEdiv : E ^ 2 / E ≤
        lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) * P := by
      apply (div_le_iff₀ hEpos).2
      calc
        E ^ 2 ≤ P * (lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) * E) := hPE
        _ = (lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) * P) * E := by ring
    have hcancel : E ^ 2 / E = E := by
      field_simp [ne_of_gt hEpos]
    rw [hcancel] at hEdiv
    simpa [E, P, a] using hEdiv

end
end ASDExplicitGamma.Variational
