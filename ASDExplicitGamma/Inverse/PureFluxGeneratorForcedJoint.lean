module

public import ASDExplicitGamma.Variational.ForcedGradient

/-! The joint forced-pair disk before the global projected-energy test. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

theorem pureFlux_forced_pair_joint_bound (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2)
    (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
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
    ∃ X : ℝ, 0 ≤ X ∧
      X + vectorWeakHaarEnergy Q W.potential ≤
        lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          blockPairingAverage (openCubeSet Q) a W W ∧
      Real.sqrt (vectorWeakHaarEnergy Q u.grad) ≤ Real.sqrt X +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) *
          lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) *
            Real.sqrt (forcedSourceCircleEnergy Q G) := by
  let U : Set (Vec 2) := openCubeSet Q
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  let M : ℕ → ℝ := lemmaVInverseDepthMax Q a
  let H0 : ℝ := lemmaVInverseHistory Q a q
  let H : ℝ := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
  let E : ℝ := blockPairingAverage U a W W
  let V : Vec 2 → Vec 2 := u.grad
  let meanV : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => V x i)
  let Vlevel : ℕ → ℝ := fun j => forcedSource_meanLevel Q j V
  let meanG : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => W.potential x i)
  let Jlevel : ℕ → ℝ := fun j => forcedSource_meanLevel Q j W.potential
  let Slevel : ℕ → ℝ := fun j => descendantsAverage Q j (fun R =>
    vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G))
  let Sweak : ℝ := (1 - w) * ∑' j : ℕ, w ^ j * Slevel j
  let Tweak : ℝ := (1 - w) * ∑' j : ℕ, w ^ j *
    forcedSource_feedback_shiftLevel Q j hEll G
  let B : ℝ := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
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
  have hJcoord (i : Fin 2) : MemLp (fun x => W.potential x i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 hWmem) i)
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
      vecNormSq (meanG R) +
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
    have hWsolR : IsBlockSolenoidalOn Vset W := by
      change IsSolenoidalOn U W.flux at hWsol
      change IsSolenoidalOn Vset W.flux
      exact hWsol.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hWfluxMemR
    have hWlowerR : MemVectorL2 Vset
        (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) :=
      hWlower.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hGmemR : MemVectorL2 Vset G :=
      hFvec.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hlocal := forcedSource_local_paired_euclidean hEllR W hWpotR hWsolR
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
    have hpotMean : pairedPotentialMean Vset W = meanG R := by
      funext i
      change volumeAverage (openCubeSet R) (fun x => W.potential x i) = _
      exact forcedSource_volumeAverage_eq_cubeAverage R _
    have hlocalMean : vecNormSq (meanG R) +
        vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G) ≤
        Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          cubeAverage R (blockPairingIntegrand a W W) := by
      change vecNormSq (pairedPotentialMean Vset W) +
        vecNormSq (pairedFluxImageMean Vset a W + pairedBesselSourceCorrectionVector hEllR G) ≤
        Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          blockPairingAverage Vset a W W at hlocal
      simpa only [hpotMean, hfluxMean, ← hshift, hpairAvg] using hlocal
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
  have hJnonneg (j : ℕ) : 0 ≤ Jlevel j := by
    unfold Jlevel forcedSource_meanLevel descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun R hR => vecNormSq_nonneg _)
  have hJointLevel (j : ℕ) : Slevel j + Jlevel j ≤ M j * E := by
    have hdef : Slevel j + Jlevel j = descendantsAverage Q j (fun R =>
        vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G) +
          vecNormSq (meanG R)) := by
      unfold Slevel Jlevel forcedSource_meanLevel
      rw [descendantsAverage_add]
    calc
      Slevel j + Jlevel j = _ := hdef
      _ ≤ descendantsAverage Q j (fun R => M j * cubeAverage R
          (blockPairingIntegrand a W W)) := descendantsAverage_le fun R hR => by
            simpa only [add_comm] using hpoint j R hR
      _ = M j * E := by
        rw [descendantsAverage_mul_left, hEnergyAverage j, hErootCube]
  have hLevel (j : ℕ) : Slevel j ≤ M j * E :=
    (le_add_of_nonneg_right (hJnonneg j)).trans (hJointLevel j)
  have hSnonneg (j : ℕ) : 0 ≤ Slevel j := by
    unfold Slevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hSdom (j : ℕ) : 0 ≤ w ^ j * Slevel j :=
    mul_nonneg (pow_nonneg hw j) (hSnonneg j)
  have hSMul : Summable (fun j : ℕ => w ^ j * (M j * E)) := by
    simpa [mul_assoc] using hMseries.mul_right E
  have hSbound (j : ℕ) : w ^ j * Slevel j ≤ w ^ j * (M j * E) :=
    mul_le_mul_of_nonneg_left (hLevel j) (pow_nonneg hw j)
  have hSseries : Summable (fun j : ℕ => w ^ j * Slevel j) :=
    Summable.of_nonneg_of_le hSdom hSbound hSMul
  have hStsum := hSseries.tsum_le_tsum hSbound hSMul
  have hH0eq : (1 - w) * (∑' j : ℕ, w ^ j * M j) = H0 := by rfl
  have hSMulEq : (∑' j : ℕ, w ^ j * (M j * E)) =
      (∑' j : ℕ, w ^ j * M j) * E := by
    calc
      _ = ∑' j : ℕ, (w ^ j * M j) * E := by
        apply tsum_congr
        intro j
        ring
      _ = _ := tsum_mul_right
  have hSweakBound : Sweak ≤ H0 * E := by
    dsimp [Sweak]
    calc
      (1 - w) * ∑' j : ℕ, w ^ j * Slevel j ≤
          (1 - w) * ∑' j : ℕ, w ^ j * (M j * E) :=
        mul_le_mul_of_nonneg_left hStsum hw1
      _ = ((1 - w) * ∑' j : ℕ, w ^ j * M j) * E := by
        rw [hSMulEq]
        ring
      _ = H0 * E := by rw [hH0eq]
  have hSweakNonneg : 0 ≤ Sweak :=
    mul_nonneg hw1 (tsum_nonneg hSdom)
  have hJseries : Summable (fun j : ℕ => w^j*Jlevel j) := by
    simpa only [w, q, Jlevel] using forcedSource_meanLevel_series_summable Q hJcoord
  have hJWeakEq : vectorWeakHaarEnergy Q W.potential =
      (1-w)*∑' j : ℕ, w^j*Jlevel j := by
    simpa only [w, q, Jlevel] using forcedSource_weakEnergy_eq_meanSeries Q hJcoord
  have hSJseries : Summable (fun j : ℕ => w^j*(Slevel j+Jlevel j)) := by
    simpa only [mul_add] using hSseries.add hJseries
  have hSJbound (j : ℕ) : w^j*(Slevel j+Jlevel j) ≤ w^j*(M j*E) :=
    mul_le_mul_of_nonneg_left (hJointLevel j) (pow_nonneg hw j)
  have hJointWeak : Sweak+vectorWeakHaarEnergy Q W.potential ≤ H0*E := by
    calc
      Sweak+vectorWeakHaarEnergy Q W.potential =
          (1-w)*∑' j : ℕ, w^j*(Slevel j+Jlevel j) := by
        rw [hJWeakEq]
        dsimp only [Sweak]
        rw [← mul_add, ← hSseries.tsum_add hJseries]
        congr 1
        apply tsum_congr
        intro j
        ring
      _ ≤ (1-w)*∑' j : ℕ, w^j*(M j*E) :=
        mul_le_mul_of_nonneg_left (hSJseries.tsum_le_tsum hSJbound hSMul) hw1
      _ = H0*E := by rw [hSMulEq]; rw [← mul_assoc, hH0eq]
  have hVSeries : Summable (fun j : ℕ => w ^ j * Vlevel j) := by
    simpa [w, q, Vlevel] using forcedSource_meanLevel_series_summable Q hVcoord
  have hVWeakEq : vectorWeakHaarEnergy Q V =
      (1 - w) * ∑' j : ℕ, w ^ j * Vlevel j := by
    simpa [w, q, Vlevel] using forcedSource_weakEnergy_eq_meanSeries Q hVcoord
  have hShiftData := forcedSource_feedback_shift_weakEnergy_le Q hEll hG hGpos
  have hTweakBound : Tweak ≤ w * H ^ 2 * forcedSourceCircleEnergy Q G := by
    simpa [Tweak, w, H, q] using hShiftData.2
  have hTweakNonneg : 0 ≤ Tweak := by
    dsimp [Tweak]
    apply mul_nonneg hw1
    apply tsum_nonneg
    intro j
    apply mul_nonneg (pow_nonneg hw j)
    unfold forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let α : ℝ := (Real.sqrt (Real.sqrt 3))⁻¹
  have hαnonneg : 0 ≤ α := by dsimp [α]; positivity
  have hαsq : α ^ 2 = w := by
    dsimp [α, w, q]
    calc
      (Real.sqrt (Real.sqrt 3))⁻¹ ^ 2 =
          ((Real.sqrt (Real.sqrt 3)) ^ 2)⁻¹ := by rw [← inv_pow]
      _ = (Real.sqrt 3)⁻¹ := by rw [Real.sq_sqrt (Real.sqrt_nonneg 3)]
  have hαroot : Real.sqrt w = α := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg w) hαnonneg).1
    calc
      (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw
      _ = α ^ 2 := hαsq.symm
  have hTroot : Real.sqrt Tweak ≤ Real.sqrt w * H *
      Real.sqrt (forcedSourceCircleEnergy Q G) := by
    have hradEq : Real.sqrt (w * H ^ 2 * forcedSourceCircleEnergy Q G) =
        Real.sqrt w * H * Real.sqrt (forcedSourceCircleEnergy Q G) := by
      calc
        Real.sqrt (w * H ^ 2 * forcedSourceCircleEnergy Q G) =
            Real.sqrt (w * (H ^ 2 * forcedSourceCircleEnergy Q G)) := by ring_nf
        _ = Real.sqrt w * Real.sqrt (H ^ 2 * forcedSourceCircleEnergy Q G) :=
          Real.sqrt_mul hw _
        _ = Real.sqrt w * (Real.sqrt (H ^ 2) *
              Real.sqrt (forcedSourceCircleEnergy Q G)) := by
          rw [Real.sqrt_mul (sq_nonneg H)]
        _ = Real.sqrt w * H * Real.sqrt (forcedSourceCircleEnergy Q G) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
            (lemmaVInverseHistory_nonneg Q a
              (Real.one_lt_rpow (by norm_num) (by norm_num)))]
          ring
    rw [← hradEq]
    exact Real.sqrt_le_sqrt hTweakBound
  have hVsumSq (j : ℕ) : 0 ≤ (1 - w) * w ^ j * Vlevel j := by
    apply mul_nonneg (mul_nonneg hw1 (pow_nonneg hw j))
    unfold Vlevel forcedSource_meanLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hSsumSq (j : ℕ) : 0 ≤ (1 - w) * w ^ j * Slevel j :=
    mul_nonneg (mul_nonneg hw1 (pow_nonneg hw j)) (hSnonneg j)
  have hTsumSq (j : ℕ) : 0 ≤ (1 - w) * w ^ j *
      forcedSource_feedback_shiftLevel Q j hEll G := by
    apply mul_nonneg (mul_nonneg hw1 (pow_nonneg hw j))
    unfold forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let av : ℕ → ℝ := fun j => Real.sqrt ((1 - w) * w ^ j * Vlevel j)
  let as : ℕ → ℝ := fun j => Real.sqrt ((1 - w) * w ^ j * Slevel j)
  let aShift : ℕ → ℝ := fun j => Real.sqrt ((1 - w) * w ^ j *
    forcedSource_feedback_shiftLevel Q j hEll G)
  have hav : Summable (fun j : ℕ => (av j) ^ 2) := by
    have h := hVSeries.mul_left (1 - w)
    have heq : (fun j => (av j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * Vlevel j)) := by
      funext j
      dsimp [av]
      rw [Real.sq_sqrt (hVsumSq j)]
      ring
    rw [heq]
    exact h
  have has : Summable (fun j : ℕ => (as j) ^ 2) := by
    have h := hSseries.mul_left (1 - w)
    have heq : (fun j => (as j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * Slevel j)) := by
      funext j
      dsimp [as]
      rw [Real.sq_sqrt (hSsumSq j)]
      ring
    rw [heq]
    exact h
  have hShiftSeries : Summable (fun j : ℕ => w ^ j *
      forcedSource_feedback_shiftLevel Q j hEll G) := hShiftData.1
  have hat : Summable (fun j : ℕ => (aShift j) ^ 2) := by
    have h := hShiftSeries.mul_left (1 - w)
    have heq : (fun j => (aShift j) ^ 2) =
        (fun j => (1 - w) * (w ^ j *
          forcedSource_feedback_shiftLevel Q j hEll G)) := by
      funext j
      dsimp [aShift]
      rw [Real.sq_sqrt (hTsumSq j)]
      ring
    rw [heq]
    exact h
  have hLevelTriangle (j : ℕ) :
      Real.sqrt (Vlevel j) ≤ Real.sqrt (Slevel j) +
        Real.sqrt (forcedSource_feedback_shiftLevel Q j hEll G) := by
    have hagg := sqrt_descendantsAverage_energy_bound_three Q j
      (fun R => vecNormSq (meanV R))
      (fun R => vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G))
      (fun R => vecNormSq (forcedSource_feedback_shift Q j R hEll G))
      (fun _ => 0) (A := 1) (B := 1) (C := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => by simp)
      (fun R hR => by
        simpa using forcedSource_sqrt_vecNormSq_sub_le
          (meanV R) (forcedSource_feedback_shift Q j R hEll G))
    simpa [Vlevel, Slevel, forcedSource_meanLevel,
      forcedSource_feedback_shiftLevel] using hagg
  have hab (j : ℕ) : av j ≤ as j + aShift j := by
    have hc : 0 ≤ (1 - w) * w ^ j := mul_nonneg hw1 (pow_nonneg hw j)
    change Real.sqrt ((1 - w) * w ^ j * Vlevel j) ≤
      Real.sqrt ((1 - w) * w ^ j * Slevel j) +
        Real.sqrt ((1 - w) * w ^ j *
          forcedSource_feedback_shiftLevel Q j hEll G)
    calc
      Real.sqrt ((1 - w) * w ^ j * Vlevel j) =
          Real.sqrt ((1 - w) * w ^ j) * Real.sqrt (Vlevel j) :=
        Real.sqrt_mul hc _
      _ ≤ Real.sqrt ((1 - w) * w ^ j) *
          (Real.sqrt (Slevel j) +
            Real.sqrt (forcedSource_feedback_shiftLevel Q j hEll G)) :=
        mul_le_mul_of_nonneg_left (hLevelTriangle j) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
        ring
  have htriangle := sqrt_tsum_sq_le_of_pointwise
    (a := as) (b := aShift) (c := av) has hat
    (fun j => Real.sqrt_nonneg _) hab
  have havEq : (∑' j : ℕ, (av j) ^ 2) = vectorWeakHaarEnergy Q V := by
    calc
      _ = (1 - w) * ∑' j : ℕ, w ^ j * Vlevel j := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro j
        dsimp [av]
        rw [Real.sq_sqrt (hVsumSq j)]
        ring
      _ = vectorWeakHaarEnergy Q V := hVWeakEq.symm
  have hasEq : (∑' j : ℕ, (as j) ^ 2) = Sweak := by
    dsimp [Sweak]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [as]
    rw [Real.sq_sqrt (hSsumSq j)]
    ring
  have hatEq : (∑' j : ℕ, (aShift j) ^ 2) = Tweak := by
    dsimp [Tweak]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [aShift]
    rw [Real.sq_sqrt (hTsumSq j)]
    ring
  have hWeakTriangle : Real.sqrt (vectorWeakHaarEnergy Q V) ≤
      Real.sqrt Sweak + Real.sqrt Tweak := by
    rw [← havEq, ← hasEq, ← hatEq]
    exact htriangle.2
  have hH0le : H0 ≤ H := by
    have hq₂ : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have hqcomp : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 3 := by
      calc
        (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
    have hInv : (Real.sqrt 3)⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hqcomp
    simpa [H0, H, q] using
      lemmaVInverseHistory_le_of_inverse_discount Q hEll hq hq₂ hInv
  have hEnergyRoot : Real.sqrt Sweak ≤ Real.sqrt H * Real.sqrt E := by
    calc
      Real.sqrt Sweak ≤ Real.sqrt (H0 * E) := Real.sqrt_le_sqrt hSweakBound
      _ ≤ Real.sqrt (H * E) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_right hH0le hEnonneg)
      _ = Real.sqrt H * Real.sqrt E := Real.sqrt_mul
        (lemmaVInverseHistory_nonneg Q a
          (Real.one_lt_rpow (by norm_num) (by norm_num))) E
  have hroot : Real.sqrt (Real.sqrt 3) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    calc
      ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
          (3 : ℝ) ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
      _ = (3 : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  have hAlphaForm : (Real.sqrt (Real.sqrt 3))⁻¹ =
      (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), hroot]
  have hAlphaExact : α = (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    simpa [α] using hAlphaForm
  have hShift : Real.sqrt Tweak ≤ α * H *
      Real.sqrt (forcedSourceCircleEnergy Q G) := by
    calc
      Real.sqrt Tweak ≤ Real.sqrt w * H *
          Real.sqrt (forcedSourceCircleEnergy Q G) := hTroot
      _ = α * H * Real.sqrt (forcedSourceCircleEnergy Q G) := by
        rw [hαroot]
  refine ⟨Sweak, hSweakNonneg, ?_, ?_⟩
  · have hj := hJointWeak.trans (mul_le_mul_of_nonneg_right hH0le hEnonneg)
    simpa only [H, E, U] using hj
  · have hv := hWeakTriangle.trans (add_le_add le_rfl hShift)
    simpa only [V, H, hAlphaExact] using hv


end
end ASDExplicitGamma.Inverse
