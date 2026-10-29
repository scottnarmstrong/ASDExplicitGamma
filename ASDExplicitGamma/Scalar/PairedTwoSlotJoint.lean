module

public import ASDExplicitGamma.Scalar.PairedTwoSlotLevel

/-! Two-slot joint forced weak estimate for a paired block field on one cube. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

theorem forced_two_slot_local_euclidean
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    {H : Vec 2 → Vec 2} (hH : MemVectorL2 (openCubeSet Q) H)
    (hWsol : IsSolenoidalOn (openCubeSet Q) (fun x => W.flux x - H x))
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval)
    (hWlower : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {F : Vec 2 → Vec 2} (hF : MemVectorL2 (openCubeSet Q) F)
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (F x))) :
    vecNormSq (pairedPotentialMean (openCubeSet Q) W +
        pairedBesselSourceCorrectionVector hEll H) +
      vecNormSq (pairedFluxImageMean (openCubeSet Q) a W +
        pairedBesselSourceCorrectionVector hEll F) ≤
      Book.Ch02.matrixNorm (coarseBlockMatrix (openCubeSet Q) a).lowerRight *
        blockPairingAverage (openCubeSet Q) a W W := by
  let U := openCubeSet Q
  let D : Mat 2 := (coarseBlockMatrix U a).lowerRight
  let p := pairedPotentialMean U W + pairedBesselSourceCorrectionVector hEll H
  let q := pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll F
  let forcedSourceLocalFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨_, hCoarse, _, _, _, _, hDpos, _⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hD : D.PosDef := by
    change (coarseBlockMatrix U a).lowerRight.PosDef
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDleft : ∀ ξ : Vec 2, matVecMul D (matVecMul D⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hBessel := pairedBessel_forced_two_slot hEll W hWpot hH hWsol hWmem
    hWlower hF hforced
  have hmetricP := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hDleft p
  have hmetricQ := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hDleft q
  have hnorm : vecNormSq p + vecNormSq q ≤ Book.Ch02.matrixNorm D *
      (vecDot p (matVecMul D⁻¹ p) + vecDot q (matVecMul D⁻¹ q)) := by
    calc
      _ ≤ Book.Ch02.matrixNorm D * vecDot p (matVecMul D⁻¹ p) +
          Book.Ch02.matrixNorm D * vecDot q (matVecMul D⁻¹ q) := add_le_add hmetricP hmetricQ
      _ = _ := by ring
  have hb : 0 ≤ Book.Ch02.matrixNorm D := Book.Ch02.matrixNorm_nonneg D
  calc
    vecNormSq (pairedPotentialMean U W + pairedBesselSourceCorrectionVector hEll H) + vecNormSq
        (pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll F) =
      vecNormSq p + vecNormSq q := by rfl
    _ ≤ Book.Ch02.matrixNorm D *
        (vecDot p (matVecMul D⁻¹ p) + vecDot q (matVecMul D⁻¹ q)) := hnorm
    _ ≤ Book.Ch02.matrixNorm D * blockPairingAverage U a W W :=
      mul_le_mul_of_nonneg_left hBessel hb


/-- Two-slot joint forced estimate: the potential of the block field is controlled
with the flux-slot source `H` and its reciprocal gradient with the potential-slot
source `G`, the two pure energies adding up to one history times the pair energy. -/
theorem forced_two_slot_joint_bound (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2)
    (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    {H : Vec 2 → Vec 2}
    (hH : MemLp H 2 (normalizedCubeMeasure Q))
    (hHpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => H x i))))
    (hWsol : IsSolenoidalOn (openCubeSet Q) (fun x => W.flux x - H x))
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval)
    (hWlower : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {G : Vec 2 → Vec 2}
    (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hGpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => G x i))))
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (G x)))
    (u : H1Function (openCubeSet Q))
    (hu : (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] u.grad) :
    ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧
      X + Y ≤ lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        blockPairingAverage (openCubeSet Q) a W W ∧
      Real.sqrt (vectorWeakHaarEnergy Q W.potential) ≤ Real.sqrt X +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) *
          lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) *
            Real.sqrt (forcedSourceCircleEnergy Q H) ∧
      Real.sqrt (vectorWeakHaarEnergy Q u.grad) ≤ Real.sqrt Y +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) *
          lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) *
            Real.sqrt (forcedSourceCircleEnergy Q G) := by
  let U : Set (Vec 2) := openCubeSet Q
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  let M : ℕ → ℝ := lemmaVInverseDepthMax Q a
  let H0 : ℝ := lemmaVInverseHistory Q a q
  let B : ℝ := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
  let E : ℝ := blockPairingAverage U a W W
  let V : Vec 2 → Vec 2 := u.grad
  let P : Vec 2 → Vec 2 := W.potential
  let meanV : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => V x i)
  let meanP : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => P x i)
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : 0 ≤ 1 - w := by
    have hlt : w < 1 := (inv_lt_one₀ (by positivity)).2 hq
    linarith
  have hEnonneg : 0 ≤ E := by
    dsimp [E, U]
    exact compatible_blockPairingAverage_nonneg hEll W
  letI forcedSourceGradientFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hFvec : MemVectorL2 U G :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hG
  have hVcoord (i : Fin 2) :
      MemLp (fun x => V x i) 2 (normalizedCubeMeasure Q) :=
    u.grad_memL2_normalizedCubeMeasure i
  have hPcoord (i : Fin 2) : MemLp (fun x => P x i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 hWmem) i)
  have hHvec : MemVectorL2 U H :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hH
  have hIntOpen : IntegrableOn (blockPairingIntegrand a W W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hWmem hEll
  have hIntCube : IntegrableOn (blockPairingIntegrand a W W) (cubeSet Q) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hIntOpen
  have hErootCube : cubeAverage Q (blockPairingIntegrand a W W) = E := by
    rw [cubeAverage_eq_integralAverage_openCubeSet Q]
    rfl
  have hEnergyAverage (j : ℕ) :
      descendantsAverage Q j (fun R => cubeAverage R (blockPairingIntegrand a W W)) =
        cubeAverage Q (blockPairingIntegrand a W W) := by
    exact (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j
      (blockPairingIntegrand a W W) hIntCube).symm
  have hMseries : Summable (fun j : ℕ => w ^ j * M j) := by
    simpa [M, w, q] using lemmaVInverseHistory_summable Q hEll hq
  have hpoint (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) :
      vecNormSq (meanP R + forcedSource_feedback_shift Q j R hEll H) +
        vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G) ≤
        M j * cubeAverage R (blockPairingIntegrand a W W) := by
    let Vset : Set (Vec 2) := openCubeSet R
    let hEllR : IsEllipticFieldOn lam Lam Vset a :=
      hEll.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    let forcedSourceDescendantFiniteMeasure : IsFiniteMeasure (volumeMeasureOn Vset) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    have hRQ : Vset ⊆ U :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hWmemR : MemBlockL2 Vset W.eval :=
      hWmem.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hWpotentialMemR : MemVectorL2 Vset W.potential :=
      memVectorL2_fst_of_memBlockL2 hWmemR
    have hWfluxMemR : MemVectorL2 Vset W.flux :=
      memVectorL2_snd_of_memBlockL2 hWmemR
    have hWpotR : IsBlockPotentialOn Vset W := by
      change IsPotentialOn U W.potential at hWpot
      change IsPotentialOn Vset W.potential
      obtain ⟨z, hz⟩ := hWpot
      have hgradMemR : MemVectorL2 Vset z.grad := by
        simpa only [hz] using hWpotentialMemR
      simpa only [hz] using z.isPotentialOn.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hgradMemR
    have hWsolR : IsSolenoidalOn Vset (fun x => W.flux x - H x) := by
      exact hWsol.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ
        (hWfluxMemR.sub (hHvec.mono_measure (Measure.restrict_mono_set volume hRQ)))
    have hHmemR : MemVectorL2 Vset H :=
      hHvec.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hWlowerR : MemVectorL2 Vset
        (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) :=
      hWlower.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hGmemR : MemVectorL2 Vset G :=
      hFvec.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hlocal := forced_two_slot_local_euclidean hEllR W hWpotR hHmemR hWsolR
      hWmemR hWlowerR hGmemR
      (forcedSource_weakEquation_onDescendant Q j R hR W G hforced)
    have hVae : (fun x => (blockMatVecMul (blockCoeffField a x)
        (W.eval x)).2) =ᵐ[volumeMeasureOn Vset] V := by
      exact ae_restrict_of_ae_restrict_of_subset hRQ hu
    have hfluxMean : pairedFluxImageMean Vset a W = meanV R := by
      calc
        pairedFluxImageMean Vset a W = volumeAverageVec Vset
            (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) := rfl
        _ = volumeAverageVec Vset V := forcedSource_volumeAverageVec_congr_ae hVae
        _ = meanV R := by
          funext i
          change volumeAverage (openCubeSet R) (fun x => V x i) = _
          rw [forcedSource_volumeAverage_eq_cubeAverage]
    have hpairAvg : blockPairingAverage Vset a W W =
        cubeAverage R (blockPairingIntegrand a W W) := by
      rw [blockPairingAverage, cubeAverage_eq_integralAverage_openCubeSet]
      rfl
    have hshift : forcedSource_feedback_shift Q j R hEll G =
        pairedBesselSourceCorrectionVector hEllR G := by
      simp [forcedSource_feedback_shift, hR]
    have hshiftH : forcedSource_feedback_shift Q j R hEll H =
        pairedBesselSourceCorrectionVector hEllR H := by
      simp [forcedSource_feedback_shift, hR]
    have hpotMean : pairedPotentialMean Vset W = meanP R := by
      funext i
      change volumeAverage (openCubeSet R) (fun x => W.potential x i) = _
      exact forcedSource_volumeAverage_eq_cubeAverage R _
    have hlocalMean : vecNormSq (meanP R + forcedSource_feedback_shift Q j R hEll H) +
        vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G) ≤
        Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          cubeAverage R (blockPairingIntegrand a W W) := by
      change vecNormSq (pairedPotentialMean Vset W + pairedBesselSourceCorrectionVector hEllR H) +
        vecNormSq (pairedFluxImageMean Vset a W + pairedBesselSourceCorrectionVector hEllR G) ≤
        Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          blockPairingAverage Vset a W W at hlocal
      simpa only [hpotMean, hfluxMean, ← hshift, ← hshiftH, hpairAvg] using hlocal
    have hvolR : 0 < (MeasureTheory.volume Vset).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos R
    obtain ⟨_, hCoarseR, _, _, _, _, _, _⟩ :=
      exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet R) hEllR hvolR
    have hsup : Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight ≤ M j := by
      have hsup' : Book.Ch02.matrixNorm (sigmaStarInvCoarse Vset a) ≤ M j := by
        unfold M lemmaVInverseDepthMax Book.Ch02.finsetSupReal
        exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hR, rfl⟩
      simpa [Vset, coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarseR] using hsup'
    have henergyR : 0 ≤ cubeAverage R (blockPairingIntegrand a W W) := by
      rw [← hpairAvg]
      exact compatible_blockPairingAverage_nonneg hEllR W
    calc
      _ ≤ Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          cubeAverage R (blockPairingIntegrand a W W) := hlocalMean
      _ ≤ M j * cubeAverage R (blockPairingIntegrand a W W) :=
        mul_le_mul_of_nonneg_right hsup henergyR
  have hS1nonneg (j : ℕ) : 0 ≤ shiftedLevel Q hEll P H j := by
    unfold shiftedLevel descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun R hR => vecNormSq_nonneg _)
  have hS2nonneg (j : ℕ) : 0 ≤ shiftedLevel Q hEll V G j := by
    unfold shiftedLevel descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun R hR => vecNormSq_nonneg _)
  have hJoint (j : ℕ) : shiftedLevel Q hEll P H j + shiftedLevel Q hEll V G j ≤ M j * E := by
    have hdef : shiftedLevel Q hEll P H j + shiftedLevel Q hEll V G j =
        descendantsAverage Q j (fun R =>
          vecNormSq (meanP R + forcedSource_feedback_shift Q j R hEll H) +
          vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G)) := by
      unfold shiftedLevel
      rw [descendantsAverage_add]
    calc
      _ = _ := hdef
      _ ≤ descendantsAverage Q j (fun R => M j * cubeAverage R
          (blockPairingIntegrand a W W)) := descendantsAverage_le fun R hR => hpoint j R hR
      _ = M j * E := by
        rw [descendantsAverage_mul_left, hEnergyAverage j, hErootCube]
  have hSMul : Summable (fun j : ℕ => w ^ j * (M j * E)) := by
    simpa [mul_assoc] using hMseries.mul_right E
  have hbd (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (hle : ∀ j, c j ≤ M j * E) :
      Summable (fun j : ℕ => w ^ j * c j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hw j) (hc j))
      (fun j => mul_le_mul_of_nonneg_left (hle j) (pow_nonneg hw j)) hSMul
  have h1le (j : ℕ) : shiftedLevel Q hEll P H j ≤ M j * E :=
    (le_add_of_nonneg_right (hS2nonneg j)).trans (hJoint j)
  have h2le (j : ℕ) : shiftedLevel Q hEll V G j ≤ M j * E :=
    (le_add_of_nonneg_left (hS1nonneg j)).trans (hJoint j)
  have hs1 := hbd _ hS1nonneg h1le
  have hs2 := hbd _ hS2nonneg h2le
  have hsum : shiftedWeak Q hEll P H + shiftedWeak Q hEll V G ≤ H0 * E := by
    unfold shiftedWeak
    have hSJ : Summable (fun j : ℕ => w ^ j * (shiftedLevel Q hEll P H j +
        shiftedLevel Q hEll V G j)) := by
      simpa only [mul_add] using hs1.add hs2
    have hcmp := hSJ.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hJoint j)
      (pow_nonneg hw j)) hSMul
    have hMeq : (∑' j : ℕ, w ^ j * (M j * E)) = (∑' j : ℕ, w ^ j * M j) * E := by
      calc
        _ = ∑' j : ℕ, (w ^ j * M j) * E := tsum_congr fun j => by ring
        _ = _ := tsum_mul_right
    have hexp : (1 - w) * ∑' j : ℕ, w ^ j * shiftedLevel Q hEll P H j +
        (1 - w) * ∑' j : ℕ, w ^ j * shiftedLevel Q hEll V G j =
        (1 - w) * ∑' j : ℕ, w ^ j * (shiftedLevel Q hEll P H j +
          shiftedLevel Q hEll V G j) := by
      rw [← mul_add, ← hs1.tsum_add hs2]
      congr 1
      exact tsum_congr fun j => by ring
    show (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ, (Real.sqrt 3)⁻¹ ^ j * _ +
      (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ, (Real.sqrt 3)⁻¹ ^ j * _ ≤ H0 * E
    change (1 - w) * ∑' j : ℕ, w ^ j * shiftedLevel Q hEll P H j +
      (1 - w) * ∑' j : ℕ, w ^ j * shiftedLevel Q hEll V G j ≤ H0 * E
    rw [hexp]
    calc
      _ ≤ (1 - w) * ∑' j : ℕ, w ^ j * (M j * E) := mul_le_mul_of_nonneg_left hcmp hw1
      _ = H0 * E := by rw [hMeq, ← mul_assoc]; rfl
  have hH0le : H0 ≤ B := by
    have hq₂ : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have hqcomp : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 3 := by
      calc
        (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
    have hInv : (Real.sqrt 3)⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hqcomp
    simpa [H0, B, q] using
      lemmaVInverseHistory_le_of_inverse_discount Q hEll hq hq₂ hInv
  refine ⟨shiftedWeak Q hEll P H, shiftedWeak Q hEll V G, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg hw1 (tsum_nonneg fun j => mul_nonneg (pow_nonneg hw j) (hS1nonneg j))
  · exact mul_nonneg hw1 (tsum_nonneg fun j => mul_nonneg (pow_nonneg hw j) (hS2nonneg j))
  · exact hsum.trans (mul_le_mul_of_nonneg_right hH0le hEnonneg)
  · exact weak_shift_triangle Q hEll hPcoord hH hHpos hs1
  · exact weak_shift_triangle Q hEll hVcoord hG hGpos hs2

end
end ASDExplicitGamma.Variational
