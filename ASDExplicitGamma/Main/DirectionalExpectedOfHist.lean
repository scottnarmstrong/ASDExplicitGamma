module

public import ASDExplicitGamma.Main.DirectionalExpected
public import ASDExplicitGamma.Main.DirectionalPhysicalFluxOfHist
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! Successors of `DirectionalExpected` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Scalar
open ASDExplicitGamma.Response ASDExplicitGamma.Native
open ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

local instance mainDirectionalExpectedFiniteEnergyVolume_ofHist (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

local instance mainDirectionalExpectedVolumeSeparable_ofHist (Q : TriadicCube 2) :
    IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance

local instance mainDirectionalExpectedFactTwoLe_ofHist : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

local instance mainDirectionalExpectedFactTwoNeTop_ofHist : Fact ((2 : ℝ≥0∞) ≠ ⊤) :=
  ⟨by simp⟩

local instance mainDirectionalExpectedHilbertBlockSecondCountable_ofHist (Q : TriadicCube 2) :
    SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance

private theorem main_expected_bilin_polarization {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (x y : V) :
    4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) := by
  have hp : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [B.map_add₂]
    rw [(B x).map_add, (B y).map_add]
    ring
  have hm : B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
    rw [B.map_sub₂]
    rw [(B x).map_sub, (B y).map_sub]
    ring
  rw [hp, hm, hB y x]
  ring

private noncomputable def main_expected_pullback_bilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : V →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR V B).flip T).comp T

private theorem main_expected_scalar_frame_energy_eq_pullback
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin =
      main_expected_pullback_bilin
        (scalarFrameRealization Q ν σ hν hσ
          (0 : ResponseCoefficient (openCubeSet Q))).energyBilin
        (1 + responseShearL2Operator σ hσ k) := by
  let U := openCubeSet Q
  let Bk := (scalarFrameRealization Q ν σ hν hσ k).energyBilin
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient U)).energyBilin
  let T := (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
    responseShearL2Operator σ hσ k
  have hBk : ∀ x y, Bk x y = Bk y x := fun x y =>
    (scalarFrameRealization Q ν σ hν hσ k).energySymm x y
  have hB0 : ∀ x y, B0 x y = B0 y x := fun x y =>
    (scalarFrameRealization Q ν σ hν hσ
      (0 : ResponseCoefficient U)).energySymm x y
  have hdiag (x : HilbertBlockL2 U) : Bk x x = B0 (T x) (T x) := by
    let hvol : 0 < (volume U).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos Q
    change (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
      hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin x x =
      (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        hvol ν σ hν hσ (0 : ResponseCoefficient U)).toMuHilbertRealization.energyBilin
        (T x) (T x)
    have hshear := responseFrameMu_energy_shear_identity
      (measurableSet_openCubeSet Q) hvol ν σ hν hσ
      (0 : ResponseCoefficient U) k x
    rw [zero_add] at hshear
    have hT : T x = x + responseShearL2Operator σ hσ k x := by
      simp [T]
    simpa only [hT] using hshear.symm
  have hpair (x y : HilbertBlockL2 U) : Bk x y = B0 (T x) (T y) := by
    have hleft := main_expected_bilin_polarization Bk hBk x y
    have hright := main_expected_bilin_polarization B0 hB0 (T x) (T y)
    have hadd : T (x + y) = T x + T y := T.map_add x y
    have hsub : T (x - y) = T x - T y := T.map_sub x y
    rw [hdiag (x + y), hdiag (x - y)] at hleft
    rw [hadd, hsub] at hleft
    calc
      Bk x y = (4 * Bk x y) / 4 := by ring
      _ = (4 * B0 (T x) (T y)) / 4 := by rw [hleft, ← hright]
      _ = B0 (T x) (T y) := by ring
  ext x y
  change Bk x y = B0 (T x) (T y)
  exact hpair x y

private theorem continuous_main_expected_pullback_bilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous fun T : V →L[ℝ] V => main_expected_pullback_bilin B T := by
  fun_prop [main_expected_pullback_bilin]

private noncomputable def main_expected_bilin_to_operator {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] V :=
  ContinuousLinearMap.compL ℝ V (V →L[ℝ] ℝ) V
    (((InnerProductSpace.toDual ℝ V).symm).toContinuousLinearEquiv
      |>.toContinuousLinearMap)

private theorem main_expected_bilin_to_operator_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    main_expected_bilin_to_operator B =
      InnerProductSpace.continuousLinearMapOfBilin B := by
  ext x
  simp [main_expected_bilin_to_operator,
    InnerProductSpace.continuousLinearMapOfBilin]

private theorem measurable_main_scalar_frame_energy_bilin
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (coeff : CutoffSample 2 → ResponseCoefficient (openCubeSet Q))
    (hcoeff : Measurable coeff) :
    Measurable fun ω : CutoffSample 2 =>
      (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin := by
  let U := openCubeSet Q
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient U)).energyBilin
  let Fk : ResponseCoefficient U →
      HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ := fun k =>
    main_expected_pullback_bilin B0 (1 + responseShearL2Operator σ hσ k)
  have hS : Continuous fun k : ResponseCoefficient U =>
      responseShearL2Operator σ hσ k :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  have hFk : Continuous Fk := by
    have hT : Continuous fun k : ResponseCoefficient U =>
        (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
          responseShearL2Operator σ hσ k := continuous_const.add hS
    exact (continuous_main_expected_pullback_bilin B0).comp hT
  have hEq : (fun ω : CutoffSample 2 =>
      (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin) =
      fun ω => Fk (coeff ω) := by
    funext ω
    exact main_expected_scalar_frame_energy_eq_pullback
      Q ν σ hν hσ (coeff ω)
  rw [hEq]
  exact hFk.measurable.comp hcoeff

private theorem measurable_main_scalar_frame_operator
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (coeff : CutoffSample 2 → ResponseCoefficient (openCubeSet Q))
    (hcoeff : Measurable coeff) :
    Measurable fun ω : CutoffSample 2 =>
      main_expected_bilin_to_operator
        ((scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin) := by
  exact (main_expected_bilin_to_operator).continuous.measurable.comp
    (measurable_main_scalar_frame_energy_bilin
      Q ν σ hν hσ coeff hcoeff)

private theorem main_expected_scalar_frame_operator_eq_coefficient_operator
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    main_expected_bilin_to_operator
        ((scalarFrameRealization Q ν σ hν hσ k).energyBilin) =
      (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k).toMuOperatorRealization.operator := by
  let R := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  change main_expected_bilin_to_operator
      (R.toMuHilbertRealization.energyBilin) = R.toMuOperatorRealization.operator
  rw [main_expected_bilin_to_operator_apply]
  change InnerProductSpace.continuousLinearMapOfBilin
      (energyBilinOfOperator R.toMuOperatorRealization.operator) =
        R.toMuOperatorRealization.operator
  ext1 X
  symm
  apply InnerProductSpace.unique_continuousLinearMapOfBilin
  intro Y
  rfl

private theorem measurable_main_top_physical_flux_operator_apply
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (hσ : 0 < (Annealed.sigmaBar M m : ℝ)) (P : BlockVec 2) :
    Measurable fun ω : CutoffSample 2 =>
      main_expected_bilin_to_operator
        ((scalarFrameRealization Q M.nu (Annealed.sigmaBar M m)
          M.nu_pos hσ (mainInsertionSkewCoefficient m t Q ω)).energyBilin)
        (mainCutoffAffineMinimizer Q M.nu (Annealed.sigmaBar M m)
          M.nu_pos hσ m t P (memLp_const P) ω) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let coeff : CutoffSample 2 → ResponseCoefficient (openCubeSet Q) :=
    mainInsertionSkewCoefficient m t Q
  have hcoeff : Measurable coeff := measurable_mainInsertionSkewCoefficient m t Q
  have hOp := measurable_main_scalar_frame_operator
    Q M.nu σ M.nu_pos hσ coeff hcoeff
  have hMin := measurable_mainCutoffAffineMinimizer
    Q M.nu σ M.nu_pos hσ m t P (memLp_const P)
  have hEval : Continuous fun z :
      ((HilbertBlockL2 (openCubeSet Q) →L[ℝ] HilbertBlockL2 (openCubeSet Q)) ×
        HilbertBlockL2 (openCubeSet Q)) => z.1 z.2 := by
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous
  convert hEval.measurable.comp (hOp.prodMk hMin) using 1
  funext ω
  rfl

private noncomputable def mainExpectedCubeCoordAverageCLM
    (Q R : TriadicCube 2) (i : Fin 2) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] ℝ :=
  (cubeVolume R)⁻¹ • hilbertVectorL2CoordSetIntegralCLM
    (U := openCubeSet Q) (cubeSet R) (measurableSet_cubeSet R) i

private theorem mainExpectedCubeCoordAverageCLM_apply
    (Q R : TriadicCube 2) (hR : cubeSet R ⊆ cubeSet Q) (i : Fin 2)
    (F : HilbertVectorL2 (openCubeSet Q)) :
    mainExpectedCubeCoordAverageCLM Q R i F =
      cubeAverage R (fun x => F x i) := by
  change (cubeVolume R)⁻¹ *
      hilbertVectorL2CoordSetIntegralCLM
        (U := openCubeSet Q) (cubeSet R) (measurableSet_cubeSet R) i F = _
  rw [hilbertVectorL2CoordSetIntegralCLM_apply]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure, MeasureTheory.integral_smul_measure]
  have hrestrict :
      (volumeMeasureOn (openCubeSet Q)).restrict (cubeSet R) =
        volume.restrict (cubeSet R) := by
    rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact Measure.restrict_restrict_of_subset hR
  rw [show (∫ x in cubeSet R, F x i ∂volumeMeasureOn (openCubeSet Q)) =
      ∫ x in cubeSet R, F x i ∂volume from by
        rw [hrestrict]]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg R)), smul_eq_mul]

private theorem measurable_mainExpectedWeakPairingLevel
    {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    (F G : Ω → HilbertVectorL2 (openCubeSet Q))
    (hF : Measurable F) (hG : Measurable G) (i : Fin 2) (j : ℕ) :
    Measurable fun ω => descendantsAverage Q j
      (fun R => cubeAverage R (fun x => F ω x i) *
        cubeAverage R (fun x => G ω x i)) := by
  classical
  unfold descendantsAverage
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro R hR
  have hsubset : cubeSet R ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hAvgF' : Measurable fun ω =>
      mainExpectedCubeCoordAverageCLM Q R i (F ω) :=
    (mainExpectedCubeCoordAverageCLM Q R i).continuous.measurable.comp hF
  have hAvgG' : Measurable fun ω =>
      mainExpectedCubeCoordAverageCLM Q R i (G ω) :=
    (mainExpectedCubeCoordAverageCLM Q R i).continuous.measurable.comp hG
  have havgF : Measurable fun ω =>
      cubeAverage R (fun x => F ω x i) := by
    convert hAvgF' using 1
    funext ω
    exact (mainExpectedCubeCoordAverageCLM_apply Q R hsubset i (F ω)).symm
  have havgG : Measurable fun ω =>
      cubeAverage R (fun x => G ω x i) := by
    convert hAvgG' using 1
    funext ω
    exact (mainExpectedCubeCoordAverageCLM_apply Q R hsubset i (G ω)).symm
  exact havgF.mul havgG

private theorem measurable_mainExpectedWeakPairingHilbert
    {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    (F G : Ω → HilbertVectorL2 (openCubeSet Q))
    (hF : Measurable F) (hG : Measurable G) (i : Fin 2)
    (hMemF : ∀ ω, MemLp (fun x => F ω x i) 2 (normalizedCubeMeasure Q))
    :
    Measurable fun ω => mainWeakHaarPairing Q
      (fun x => F ω x i) (fun x => G ω x i) := by
  classical
  let w : ℝ := (Real.sqrt 3)⁻¹
  have hformula (ω) : mainWeakHaarPairing Q
      (fun x => F ω x i) (fun x => G ω x i) =
      (1 - w) * ∑' j : ℕ, w ^ j * descendantsAverage Q j
        (fun R => cubeAverage R (fun x => F ω x i) *
          cubeAverage R (fun x => G ω x i)) := by
    unfold mainWeakHaarPairing
    congr 1
    apply tsum_congr
    intro j
    rw [projection_selfAdjoint Q j (hMemF ω)
      (projection_memLp Q j (fun x => G ω x i) 2),
      projection_idempotent Q j (fun x => G ω x i),
      pairing_projection_right Q j (g := fun x => G ω x i)
        (hf := hMemF ω)]
  have hsum : Measurable fun ω => ∑' j : ℕ, w ^ j *
      descendantsAverage Q j
        (fun R => cubeAverage R (fun x => F ω x i) *
          cubeAverage R (fun x => G ω x i)) := by
    apply Measurable.tsum
    intro j
    exact measurable_const.mul
      (measurable_mainExpectedWeakPairingLevel Q F G hF hG i j)
  have hEq : (fun ω => mainWeakHaarPairing Q
      (fun x => F ω x i) (fun x => G ω x i)) =
      fun ω => (1 - w) * ∑' j : ℕ, w ^ j * descendantsAverage Q j
        (fun R => cubeAverage R (fun x => F ω x i) *
          cubeAverage R (fun x => G ω x i)) := by
    funext ω
    exact hformula ω
  rw [hEq]
  exact measurable_const.mul hsum

private noncomputable def mainExpectedTopPhysicalFluxHilbertCarrier
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (hσ : 0 < (Annealed.sigmaBar M m : ℝ)) (i : Fin 2)
    (ω : CutoffSample 2) : HilbertVectorL2 (openCubeSet Q) := by
  let P : BlockVec 2 := oldSignedPairLoad false i
  exact ((volume (openCubeSet Q)).toReal • hilbertFirstProjection (openCubeSet Q))
      (main_expected_bilin_to_operator
        ((scalarFrameRealization Q M.nu (Annealed.sigmaBar M m)
          M.nu_pos hσ (mainInsertionSkewCoefficient m t Q ω)).energyBilin)
        (mainCutoffAffineMinimizer Q M.nu (Annealed.sigmaBar M m)
          M.nu_pos hσ m t P (memLp_const P) ω)) -
    hilbertFirstProjection (openCubeSet Q) (blockVecToHilbertBlockL2Const P)

private theorem measurable_mainExpectedTopPhysicalFluxHilbertCarrier
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (hσ : 0 < (Annealed.sigmaBar M m : ℝ)) (i : Fin 2) :
    Measurable (mainExpectedTopPhysicalFluxHilbertCarrier M m t Q hσ i) := by
  let P : BlockVec 2 := oldSignedPairLoad false i
  let T : HilbertBlockL2 (openCubeSet Q) →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
    (volume (openCubeSet Q)).toReal • hilbertFirstProjection (openCubeSet Q)
  have hApply := measurable_main_top_physical_flux_operator_apply
    M m t Q hσ P
  have hFirst : Measurable fun ω => T
      (main_expected_bilin_to_operator
        ((scalarFrameRealization Q M.nu (Annealed.sigmaBar M m)
          M.nu_pos hσ (mainInsertionSkewCoefficient m t Q ω)).energyBilin)
        (mainCutoffAffineMinimizer Q M.nu (Annealed.sigmaBar M m)
          M.nu_pos hσ m t P (memLp_const P) ω)) := by
    simpa only [T, Function.comp_def] using T.continuous.measurable.comp hApply
  change Measurable fun ω =>
    T (main_expected_bilin_to_operator
      ((scalarFrameRealization Q M.nu (Annealed.sigmaBar M m)
        M.nu_pos hσ (mainInsertionSkewCoefficient m t Q ω)).energyBilin)
      (mainCutoffAffineMinimizer Q M.nu (Annealed.sigmaBar M m)
        M.nu_pos hσ m t P (memLp_const P) ω)) -
      hilbertFirstProjection (openCubeSet Q) (blockVecToHilbertBlockL2Const P)
  exact hFirst.sub measurable_const

private theorem main_expected_first_projection_to_vector
    (Q : TriadicCube 2) (F : HilbertBlockL2 (openCubeSet Q)) :
    hilbertFirstProjection (openCubeSet Q) F =
      toHilbertVectorL2OfVecField
        (memVectorL2_fst_of_memBlockL2
          (Lp.memLp (hilbertBlockL2ToBlockL2 (U := openCubeSet Q) F))) := by
  apply Lp.ext
  filter_upwards [
    (PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 0 :
      HilbertBlockVec 2 →L[ℝ] HilbertVec 2).coeFn_compLpL
        F,
    coeFn_hilbertBlockL2ToBlockL2 (U := openCubeSet Q) F,
    coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_fst_of_memBlockL2
        (Lp.memLp (hilbertBlockL2ToBlockL2 (U := openCubeSet Q) F)))]
    with x hproj hblock hvec
  have hblock' : HilbertBlockVec.ofBlockVec
      (hilbertBlockL2ToBlockL2 (U := openCubeSet Q) F x) = F x := by
    simpa only [HilbertBlockVec.ofBlockVec_toBlockVec] using
      congrArg HilbertBlockVec.ofBlockVec hblock
  change ((PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 0 :
    HilbertBlockVec 2 →L[ℝ] HilbertVec 2).compLpL 2
      (volumeMeasureOn (openCubeSet Q)) F) x = _
  rw [hproj, ← hblock']
  simpa [hilbertifyVecField] using hvec.symm

private theorem main_expected_top_physical_flux_error_memVectorL2
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q)
      (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i)) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let P : BlockVec 2 := oldSignedPairLoad false i
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k
  have hCoeff : MemBlockL2 (openCubeSet Q) (fun x =>
      blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).2 k P x)) := by
    simpa [a, oldSignedFrameCanonicalField] using
      old_signed_canonical_coefficient_memL2 Q a hEll P
  have hErr := (memVectorL2_fst_of_memBlockL2 hCoeff).sub
    (memVectorL2_const P.1)
  have hErr' : MemVectorL2 (openCubeSet Q) (fun x =>
      (blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).2 k P x)).1 - P.1) := by
    have hfun : (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
            (Annealed.sigmaBar M m).2 k P x)).1) - (fun _ => P.1) =
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
              (Annealed.sigmaBar M m).2 k P x)).1 - P.1) := by
      funext x
      rfl
    rw [← hfun]
    exact hErr
  change MemVectorL2 (openCubeSet Q)
    (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i))
  simpa [mainDirectionalTopPhysicalFluxDirectionError, σ, k, a, P,
    oldSignedFrameCanonicalField, oldSignedPairLoad, blockBasis, basisVec,
    blockMatVecMul] using hErr'

private theorem main_expected_top_physical_flux_minimizer_plain
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (i : Fin 2) :
    hilbertBlockL2ToBlockL2 (mainCutoffAffineMinimizer Q M.nu
      (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar M m).2 m t
      (oldSignedPairLoad false i) (memLp_const (oldSignedPairLoad false i)) ω) =
      oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (oldSignedPairLoad false i) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let P : BlockVec 2 := oldSignedPairLoad false i
  change scalarResidualField Q M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k
      (toHilbertBlockL2OfBlockField (memLp_const P)) =
    oldSignedFrameCanonicalField Q M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k P
  have hconst : toHilbertBlockL2OfBlockField (memLp_const P) =
      (scalarFrameRealization Q M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k).constantField P := by
    rfl
  rw [hconst]
  simpa [oldSignedFrameCanonicalField] using
    old_signed_affine_residual_field Q M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).2 k P

private theorem main_expected_top_physical_flux_carrier_eq_actual
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (hσ : 0 < (Annealed.sigmaBar M m : ℝ)) (i : Fin 2)
    (ω : CutoffSample 2) :
    mainExpectedTopPhysicalFluxHilbertCarrier M m t Q hσ i ω =
      toHilbertVectorL2OfVecField
        (main_expected_top_physical_flux_error_memVectorL2 M m t Q ω i) := by
  let U := openCubeSet Q
  let σ : ℝ := Annealed.sigmaBar M m
  let V : ℝ := (volume U).toReal
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let P : BlockVec 2 := oldSignedPairLoad false i
  let H := mainCutoffAffineMinimizer Q M.nu σ M.nu_pos hσ m t P (memLp_const P) ω
  let H0 := blockVecToHilbertBlockL2Const (U := U) P
  let R := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    M.nu σ M.nu_pos hσ k
  let Y := R.toMuOperatorRealization.operator H
  let fY : Vec 2 → Vec 2 := fun x => (hilbertBlockL2ToBlockL2 (U := U) Y x).1
  let f0 : Vec 2 → Vec 2 := fun x => (hilbertBlockL2ToBlockL2 (U := U) H0 x).1
  have hV : 0 < V := by
    dsimp [V, U]
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hVne : V ≠ 0 := hV.ne'
  have hOpEq : main_expected_bilin_to_operator
      ((scalarFrameRealization Q M.nu σ M.nu_pos hσ k).energyBilin) =
      R.toMuOperatorRealization.operator :=
    main_expected_scalar_frame_operator_eq_coefficient_operator
      Q M.nu σ M.nu_pos hσ k
  have hMinPlain := main_expected_top_physical_flux_minimizer_plain
    M m t Q ω i
  have hMinAE : hilbertBlockL2ToBlockL2 (U := U) H =ᵐ[
      volumeMeasureOn U] oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P :=
    Lp.ext_iff.mp hMinPlain
  have hApply := R.toMuOperatorRealization.ae_apply H
  have hYAE : hilbertBlockL2ToBlockL2 (U := U) Y =ᵐ[volumeMeasureOn U]
      fun x => V⁻¹ • blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x) := by
    filter_upwards [hApply,
      coeFn_hilbertBlockL2ToBlockL2 (U := U) Y,
      coeFn_hilbertBlockL2ToBlockL2 (U := U) H,
      hMinAE] with x happ hY hH hMin
    calc
      hilbertBlockL2ToBlockL2 (U := U) Y x = (Y x).toBlockVec := hY
      _ = V⁻¹ • blockMatVecMul (blockCoeffField a x)
          (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x) := by
        rw [happ]
        change (V⁻¹ • HilbertBlockVec.ofBlockVec
          (blockMatVecMul (blockCoeffField a x) (H x).toBlockVec)).toBlockVec = _
        have hfield : (H x).toBlockVec =
            oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x := hH.symm.trans hMin
        apply Prod.ext
        · ext j
          simp [HilbertBlockVec.toBlockVec, HilbertVec.toVec, hfield]
        · ext j
          simp [HilbertBlockVec.toBlockVec, HilbertVec.toVec, hfield]
  have hYfst : MemVectorL2 U fY :=
    memVectorL2_fst_of_memBlockL2 (Lp.memLp (hilbertBlockL2ToBlockL2 (U := U) Y))
  have h0fst : MemVectorL2 U f0 :=
    memVectorL2_fst_of_memBlockL2 (Lp.memLp (hilbertBlockL2ToBlockL2 (U := U) H0))
  have herr : MemVectorL2 U
      (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i)) :=
    main_expected_top_physical_flux_error_memVectorL2 M m t Q ω i
  have hYfstAE : fY =ᵐ[volumeMeasureOn U] fun x =>
      V⁻¹ • (blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x)).1 := by
    filter_upwards [hYAE] with x hx
    have h := congrArg Prod.fst hx
    simpa [fY] using h
  have h0AE : f0 =ᵐ[volumeMeasureOn U] fun _ => P.1 := by
    filter_upwards [
      coeFn_hilbertBlockL2ToBlockL2 (U := U) H0,
      coeFn_blockVecToHilbertBlockL2Const (U := U) P] with x h0 hconst
    change (hilbertBlockL2ToBlockL2 (U := U) H0 x).1 = P.1
    rw [h0, hconst]
    simp
  have hCarrier : mainExpectedTopPhysicalFluxHilbertCarrier M m t Q hσ i ω =
      V • toHilbertVectorL2OfVecField hYfst -
        toHilbertVectorL2OfVecField h0fst := by
    change V • hilbertFirstProjection U
        (main_expected_bilin_to_operator
          ((scalarFrameRealization Q M.nu σ M.nu_pos hσ k).energyBilin)
          (mainCutoffAffineMinimizer Q M.nu σ M.nu_pos hσ m t P
            (memLp_const P) ω)) - hilbertFirstProjection U H0 = _
    rw [hOpEq,
      main_expected_first_projection_to_vector Q Y,
      main_expected_first_projection_to_vector Q H0]
  rw [hCarrier]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_sub (V • toHilbertVectorL2OfVecField hYfst)
      (toHilbertVectorL2OfVecField h0fst),
    Lp.coeFn_smul V (toHilbertVectorL2OfVecField hYfst),
    coeFn_toHilbertVectorL2OfVecField hYfst,
    coeFn_toHilbertVectorL2OfVecField h0fst,
    coeFn_toHilbertVectorL2OfVecField herr,
    hYfstAE, h0AE] with x hsub hscale hY h0 herrFn hYpoint h0point
  have hErrPoint : mainDirectionalTopPhysicalFluxDirectionError
      M m t Q ω (basisVec i) x =
      (blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x)).1 - P.1 := by
    simp [mainDirectionalTopPhysicalFluxDirectionError, a, k, σ, P,
      oldSignedPairLoad, blockBasis, basisVec, blockMatVecMul]
  rw [hsub]
  change (V • toHilbertVectorL2OfVecField hYfst) x -
      (toHilbertVectorL2OfVecField h0fst) x =
    (toHilbertVectorL2OfVecField herr) x
  rw [hscale]
  simp only [Pi.smul_apply]
  rw [hY, h0, herrFn]
  simp only [hilbertifyVecField]
  rw [hYpoint, h0point, hErrPoint]
  have hfac : V * V⁻¹ = 1 := by field_simp
  calc
    V • HilbertVec.ofVec
        (V⁻¹ • (blockMatVecMul (blockCoeffField a x)
          (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x)).1) -
        HilbertVec.ofVec P.1 =
      HilbertVec.ofVec
        (V • (V⁻¹ • (blockMatVecMul (blockCoeffField a x)
          (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x)).1) - P.1) := by
            simp
    _ = HilbertVec.ofVec
        ((blockMatVecMul (blockCoeffField a x)
          (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k P x)).1 - P.1) := by
            rw [smul_smul, hfac, one_smul]

private theorem main_expected_open_ae_to_cube_ae
    (Q : TriadicCube 2) {P : Vec 2 → Prop}
    (hP : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), P x) :
    ∀ᵐ x ∂volume.restrict (cubeSet Q), P x := by
  rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at hP
  exact hP

private theorem main_expected_top_carrier_coordinate_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (hσ : 0 < (Annealed.sigmaBar M m : ℝ)) (i k : Fin 2)
    (ω : CutoffSample 2) :
    (fun x => mainExpectedTopPhysicalFluxHilbertCarrier M m t Q hσ i ω x k) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    (fun x => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
      (basisVec i) x k) := by
  let hErr := main_expected_top_physical_flux_error_memVectorL2 M m t Q ω i
  have hCarrier := Lp.ext_iff.mp
    (main_expected_top_physical_flux_carrier_eq_actual M m t Q hσ i ω)
  filter_upwards [hCarrier, coeFn_toHilbertVectorL2OfVecField hErr] with x hxy hyz
  have hxyz := hxy.trans hyz
  have hk := congrArg (fun z : HilbertVec 2 => z k) hxyz
  simpa [hilbertifyVecField] using hk

private theorem main_expected_top_carrier_coordinate_memLp
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (i k : Fin 2) :
    ∀ ω, MemLp
      (fun x => mainExpectedTopPhysicalFluxHilbertCarrier M m t Q
        (Annealed.sigmaBar_characterization M m).1 i ω x k)
      2 (normalizedCubeMeasure Q) := by
  intro ω
  have hActual := main_directional_top_physical_flux_direction_memLp
    M m t Q ω (basisVec i) k
  have hOpen := main_expected_top_carrier_coordinate_ae M m t Q
    (Annealed.sigmaBar_characterization M m).1 i k ω
  have hCube := main_expected_open_ae_to_cube_ae Q hOpen
  have hNormalized :
      (fun x => mainExpectedTopPhysicalFluxHilbertCarrier M m t Q
        (Annealed.sigmaBar_characterization M m).1 i ω x k) =ᵐ[
          normalizedCubeMeasure Q]
      (fun x => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
        (basisVec i) x k) := by
    have hscaled := hCube.filter_mono
      (Measure.ae_smul_measure_le (ENNReal.ofReal ((cubeVolume Q)⁻¹)))
    change (fun x => mainExpectedTopPhysicalFluxHilbertCarrier M m t Q
        (Annealed.sigmaBar_characterization M m).1 i ω x k) =ᵐ[
          ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (cubeSet Q)]
      (fun x => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
        (basisVec i) x k) at hscaled
    exact hscaled
  exact (memLp_congr_ae hNormalized).mpr hActual

private theorem main_expected_top_physical_flux_covariance_entry_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (i j : Fin 2) :
    Measurable fun ω => mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω i j := by
  let hσ : 0 < (Annealed.sigmaBar M m : ℝ) :=
    (Annealed.sigmaBar_characterization M m).1
  let F : Fin 2 → CutoffSample 2 → HilbertVectorL2 (openCubeSet Q) := fun l ω =>
    mainExpectedTopPhysicalFluxHilbertCarrier M m t Q hσ l ω
  have hF : ∀ l, Measurable (F l) := by
    intro l
    exact measurable_mainExpectedTopPhysicalFluxHilbertCarrier M m t Q hσ l
  have hMem : ∀ l ω k,
      MemLp (fun x => F l ω x k) 2 (normalizedCubeMeasure Q) := by
    intro l ω k
    exact main_expected_top_carrier_coordinate_memLp M m t Q l k ω
  have hPair (k : Fin 2) :
      Measurable fun ω => mainWeakHaarPairing Q
        (fun x => F i ω x k) (fun x => F j ω x k) :=
    measurable_mainExpectedWeakPairingHilbert Q (F i) (F j)
      (hF i) (hF j) k (fun ω => hMem i ω k)
  have hSum : Measurable fun ω => ∑ k : Fin 2,
      mainWeakHaarPairing Q (fun x => F i ω x k) (fun x => F j ω x k) := by
    apply Finset.measurable_sum
    intro k hk
    exact hPair k
  have hEq :
      (fun ω => mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω i j) =
      fun ω => ∑ k : Fin 2,
        mainWeakHaarPairing Q (fun x => F i ω x k) (fun x => F j ω x k) := by
    funext ω
    have hFi := main_expected_open_ae_to_cube_ae Q
      (main_expected_top_carrier_coordinate_ae M m t Q hσ i (0 : Fin 2) ω)
    have hFi1 := main_expected_open_ae_to_cube_ae Q
      (main_expected_top_carrier_coordinate_ae M m t Q hσ i (1 : Fin 2) ω)
    have hFj := main_expected_open_ae_to_cube_ae Q
      (main_expected_top_carrier_coordinate_ae M m t Q hσ j (0 : Fin 2) ω)
    have hFj1 := main_expected_open_ae_to_cube_ae Q
      (main_expected_top_carrier_coordinate_ae M m t Q hσ j (1 : Fin 2) ω)
    have hFvec : (fun x k => F i ω x k) =ᵐ[volume.restrict (cubeSet Q)]
        (fun x k => mainDirectionalTopPhysicalFluxDirectionError
          M m t Q ω (basisVec i) x k) := by
      filter_upwards [hFi, hFi1] with x h0 h1
      funext k
      fin_cases k
      · exact h0
      · exact h1
    have hGvec : (fun x k => F j ω x k) =ᵐ[volume.restrict (cubeSet Q)]
        (fun x k => mainDirectionalTopPhysicalFluxDirectionError
          M m t Q ω (basisVec j) x k) := by
      filter_upwards [hFj, hFj1] with x h0 h1
      funext k
      fin_cases k
      · exact h0
      · exact h1
    change mainVectorWeakHaarPairing Q
        (fun x k => mainDirectionalTopPhysicalFluxDirectionError
          M m t Q ω (basisVec i) x k)
        (fun x k => mainDirectionalTopPhysicalFluxDirectionError
          M m t Q ω (basisVec j) x k) = _
    simpa only [mainVectorWeakHaarPairing] using
      (main_vector_weak_hair_pairing_congr_ae Q hFvec hGvec).symm
  rw [hEq]
  exact hSum

private theorem main_expected_psd_entry_norm_le_trace
    {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hN : Matrix.PosSemidef N) (hSym : ∀ i j, N i j = N j i)
    (i j : Fin 2) :
    ‖N i j‖ ≤ Matrix.trace N := by
  have h00 : 0 ≤ N 0 0 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 0)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using h
  have h11 : 0 ≤ N 1 1 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 1)
    simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] using h
  have hplus : 0 ≤ N 0 0 + 2 * N 0 1 + N 1 1 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 0 + basisVec 1)
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] at h
    rw [hSym 1 0] at h
    nlinarith only [h]
  have hminus : 0 ≤ N 0 0 - 2 * N 0 1 + N 1 1 := by
    have h := hN.dotProduct_mulVec_nonneg (basisVec 0 - basisVec 1)
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, basisVec] at h
    rw [hSym 1 0] at h
    nlinarith only [h]
  have habs : |N 0 1| ≤ N 0 0 + N 1 1 := by
    rw [abs_le]
    constructor <;> nlinarith only [hplus, hminus, h00, h11]
  have hTrace : Matrix.trace N = N 0 0 + N 1 1 := by
    simp [Matrix.trace_fin_two]
  fin_cases i <;> fin_cases j
  · change ‖N 0 0‖ ≤ Matrix.trace N
    rw [Real.norm_eq_abs, abs_of_nonneg h00, hTrace]
    exact le_add_of_nonneg_right h11
  · change ‖N 0 1‖ ≤ Matrix.trace N
    rw [Real.norm_eq_abs, hTrace]
    exact habs
  · change ‖N 1 0‖ ≤ Matrix.trace N
    calc
      ‖N 1 0‖ = ‖N 0 1‖ := by rw [hSym 1 0]
      _ ≤ Matrix.trace N := by
        rw [Real.norm_eq_abs, hTrace]
        exact habs
  · change ‖N 1 1‖ ≤ Matrix.trace N
    rw [Real.norm_eq_abs, abs_of_nonneg h11, hTrace]
    exact le_add_of_nonneg_left h00

/-- Successor of `main_source_directional_top_physical_flux_expected_matrix_bound` with the history envelope `Hfun`. -/
theorem main_source_directional_top_physical_flux_expected_matrix_bound_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      ∫ ω, mainDirectionalTopPhysicalFluxCovarianceMatrix M m t
        (originCube 2 (m - 5)) ω i j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
    A 0 1 = 0 ∧ A 1 0 = 0 ∧
      A 0 0 ≤ 2 * mainD * mainM0 (Hfun t) *
        Hfun t ∧
      A 1 1 ≤ 2 * mainD * mainM0 (Hfun t) *
        Hfun t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let N : CutoffSample 2 → Matrix (Fin 2) (Fin 2) ℝ :=
    fun ω => mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω
  let H : CutoffSample 2 → ℝ := fun ω =>
    (mainPartialInsertedTraceMaxHistory M m t ω).toReal
  let Theta : CutoffSample 2 → ℝ := fun ω =>
    4 * mainD * mainPartialInsertedMultiplierHistory M m t ω * H ω
  let xi : ℝ := 4 * mainD * mainM0 (Hfun t) *
    Hfun t
  have hEnvelope := hHist t ⟨ht0, ht1⟩
  have hHmem : MemLp H 2 μ := by
    apply (memLp_congr_ae ?_).mp hEnvelope.2.1
    filter_upwards with ω
    have heq : mainOrdinaryTraceMaxHistory M m Q t ω =
        mainPartialInsertedTraceMaxHistory M m t ω := by
      simp only [mainPartialInsertedTraceMaxHistory,
        mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
        Scalar.inverseHistoryDiscount, mainAlpha]
      rfl
    exact congrArg ENNReal.toReal heq
  have hMom := main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hgamma m hpast t ht0 ht1
  have hProduct := hMom.1.1.1.2
  have hMmem := hMom.1.2
  have hThetaInt : Integrable Theta μ := by
    have hprod : Integrable
        (fun ω => mainPartialInsertedMultiplierHistory M m t ω * H ω) μ :=
      hMmem.integrable_mul hHmem
    have hconst := hprod.const_mul (4 * mainD)
    apply hconst.congr
    filter_upwards with ω
    simp only [Theta, H]
    ring
  have hTheta : (∫ ω, Theta ω ∂μ) ≤ xi := by
    calc
      (∫ ω, Theta ω ∂μ) =
          4 * (∫ ω, mainD * mainPartialInsertedMultiplierHistory M m t ω *
            H ω ∂μ) := by
        rw [show Theta = fun ω => 4 *
          (mainD * mainPartialInsertedMultiplierHistory M m t ω * H ω) by
            funext ω
            dsimp [Theta]
            ring]
        rw [integral_const_mul]
      _ ≤ 4 * (mainD * mainM0 (Hfun t) *
          Hfun t) :=
        mul_le_mul_of_nonneg_left hProduct (by norm_num)
      _ = xi := by dsimp [xi]; ring
  have hSym : ∀ ω i j, N ω i j = N ω j i := by
    intro ω i j
    exact main_directional_top_physical_flux_covariance_matrix_symm
      M m t Q ω i j
  have hCov : ∀ ω,
      N (rotateCutoffSample quarterTurn
        main_quarterTurn_isSignedPermutation ω) =
        matTranspose quarterTurn * N ω * quarterTurn := by
    intro ω
    exact main_directional_top_physical_flux_covariance_matrix_quarterTurn
      M m t ω
  have hTrace : ∀ᵐ ω ∂μ, Matrix.trace (N ω) ≤ Theta ω := by
    have hsource :=
      main_source_directional_top_physical_flux_covariance_trace_le_multiplier_product_ofHist (Hfun := Hfun) (hHist := hHist)
        M h hM hgamma m hpast t ht0 ht1
    filter_upwards [hsource] with ω hω
    simpa [N, Q, Theta, H] using hω
  have hInt : ∀ i j, Integrable (fun ω => N ω i j) μ := by
    intro i j
    have hEntryMeas := main_expected_top_physical_flux_covariance_entry_measurable
      M m t Q i j
    apply hThetaInt.mono' hEntryMeas.aestronglyMeasurable
    filter_upwards [hTrace] with ω hω
    have hPSD := main_directional_top_physical_flux_covariance_matrix_posSemidef
      M m t Q ω
    have hSymω : ∀ i j, (N ω) i j = (N ω) j i := by
      intro i j
      exact main_directional_top_physical_flux_covariance_matrix_symm
        M m t Q ω i j
    exact (main_expected_psd_entry_norm_le_trace hPSD hSymω i j).trans hω
  have hIso := main_expected_matrix_half_trace_of_quarter_turn
    M N Theta xi hInt hSym hCov hThetaInt hTrace hTheta
  have hScale : xi / 2 =
      2 * mainD * mainM0 (Hfun t) *
        Hfun t := by
    dsimp [xi]
    ring
  rcases hIso with ⟨h01, h10, h00, h11⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [N, Q, μ] using h01
  · simpa [N, Q, μ] using h10
  · rw [← hScale]
    simpa [N, Q, μ] using h00
  · rw [← hScale]
    simpa [N, Q, μ] using h11

end ASDExplicitGamma.Main
end
