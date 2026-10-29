module

public import ASDExplicitGamma.Scalar.PhysicalResolventIdentity
public import ASDExplicitGamma.Scalar.PhysicalResolventParity
public import ASDExplicitGamma.Scalar.ResolventParityHilbert
public import ASDExplicitGamma.Scalar.ResolventGaussianParity
public import ASDExplicitGamma.Gaussian.ModelMoments
public import ASDExplicitGamma.Inverse.BankLocal
public import Mathlib.Tactic.NoncommRing

/-! Copies (renamed, made public) of the private bounds of `PhysicalResolventParity`, used for the
scaled parity argument of SC-ONE-SHELL-RECIPROCAL-DROP. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace Topology ENNReal

noncomputable section

local instance cFiniteMeasure (Q : TriadicCube 2) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem pureFluxBlockOperator_sub_eq_inserted' {α : ℝ}
    (A A' : X →L[ℝ] Y) :
    pureFluxBlockOperator α A' - pureFluxBlockOperator α A =
      pureFluxBlockOperator 0 (A' - A) := by
  have hA : A' = A + (A' - A) := by abel
  have hM : pureFluxBlockOperator α A' =
      pureFluxBlockOperator α A + pureFluxBlockOperator 0 (A' - A) := by
    exact (congrArg (pureFluxBlockOperator α) hA).trans
      (pureFluxBlockOperator_add α A (A' - A)).symm
  rw [hM]
  abel

theorem pureFluxBlockInserted_continuous' :
    Continuous (fun D : X →L[ℝ] Y => pureFluxBlockOperator 0 D) := by
  let c : NNReal := 1
  have hc : (c : ℝ) = 1 := rfl
  have hLip : LipschitzWith c
      (fun D : X →L[ℝ] Y => pureFluxBlockOperator 0 D) := by
    apply LipschitzWith.of_dist_le_mul
    intro D D'
    rw [dist_eq_norm, dist_eq_norm]
    have h := pureFluxBlockInserted_opNorm_le (D - D')
    rw [pureFluxBlockOperator_sub_eq_inserted']
    simpa only [hc, one_mul] using h
  exact hLip.continuous

theorem pureFluxBlockInverse_resolvent_identity' {α : ℝ}
    (hα : 0 < α) (A A' : X →L[ℝ] Y) :
    pureFluxBlockInverse α hα A - pureFluxBlockInverse α hα A' =
      pureFluxBlockInverse α hα A *
        (pureFluxBlockOperator α A' - pureFluxBlockOperator α A) *
          pureFluxBlockInverse α hα A' := by
  let B := pureFluxBlockInverse α hα A
  let B' := pureFluxBlockInverse α hα A'
  let T := pureFluxBlockOperator α A
  let T' := pureFluxBlockOperator α A'
  have hBT : B * T = 1 := pureFluxBlockInverse_right α hα A
  have hT'B' : T' * B' = 1 := pureFluxBlockInverse_left α hα A'
  change B - B' = B * (T' - T) * B'
  calc
    B - B' = B * 1 - 1 * B' := by simp
    _ = B * (T' * B') - (B * T) * B' := by rw [hT'B', hBT]
    _ = (B * T') * B' - (B * T) * B' := by rw [← mul_assoc]
    _ = (B * T' - B * T) * B' := by rw [sub_mul]
    _ = B * (T' - T) * B' := by rw [← mul_sub]

theorem pureFluxBlockInverse_difference_norm_le' {α : ℝ}
    (hα : 0 < α) (A A' : X →L[ℝ] Y) :
    ‖pureFluxBlockInverse α hα A - pureFluxBlockInverse α hα A'‖ ≤
      (α⁻¹) ^ 2 * ‖A - A'‖ := by
  rw [pureFluxBlockInverse_resolvent_identity' hα A A',
    pureFluxBlockOperator_sub_eq_inserted']
  have hB := pureFluxBlockInverse_opNorm_le hα A
  have hB' := pureFluxBlockInverse_opNorm_le hα A'
  have hC := pureFluxBlockInserted_opNorm_le (A' - A)
  let B := pureFluxBlockInverse α hα A
  let C := pureFluxBlockOperator 0 (A' - A)
  let B' := pureFluxBlockInverse α hα A'
  have hBC : ‖B * C‖ ≤ ‖B‖ * ‖C‖ := norm_mul_le B C
  have hBCB : ‖B * C * B'‖ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := by
    calc
      ‖B * C * B'‖ ≤ ‖B * C‖ * ‖B'‖ := norm_mul_le (B * C) B'
      _ ≤ (‖B‖ * ‖C‖) * ‖B'‖ :=
        mul_le_mul_of_nonneg_right hBC (norm_nonneg B')
  calc
    ‖B * C * B'‖ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := hBCB
    _ ≤ (α⁻¹ * ‖A' - A‖) * α⁻¹ := by gcongr
    _ = (α⁻¹) ^ 2 * ‖A - A'‖ := by rw [norm_sub_rev]; ring

theorem pureFluxBlockInverse_continuous' {α : ℝ} (hα : 0 < α) :
    Continuous (fun A : X →L[ℝ] Y => pureFluxBlockInverse α hα A) := by
  let c : NNReal := ⟨(α⁻¹) ^ 2, sq_nonneg _⟩
  have hc : (c : ℝ) = (α⁻¹) ^ 2 := rfl
  have hLip : LipschitzWith c
      (fun A : X →L[ℝ] Y => pureFluxBlockInverse α hα A) := by
    apply LipschitzWith.of_dist_le_mul
    intro A A'
    rw [dist_eq_norm, dist_eq_norm]
    simpa only [hc] using pureFluxBlockInverse_difference_norm_le' hα A A'
  exact hLip.continuous

theorem physicalProjectedCoefficient_continuous' (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun k : ResponseCoefficient (openCubeSet Q) =>
      physicalProjectedCoefficient Q σ hσ k) := by
  have hS : Continuous (fun k : ResponseCoefficient (openCubeSet Q) =>
      responseShearL2Operator σ hσ k) :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  fun_prop [physicalProjectedCoefficient, physicalPositiveShear,
    responseShearL2Operator]

theorem physicalProjectedCoefficient_neg' (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q)) :
    physicalProjectedCoefficient Q σ hσ (-H) =
      -physicalProjectedCoefficient Q σ hσ H := by
  have hzero : physicalProjectedCoefficient Q σ hσ (0 : ResponseCoefficient
      (openCubeSet Q)) = 0 := by
    have hS : responseShearL2Operator σ hσ (0 : ResponseCoefficient
        (openCubeSet Q)) = 0 :=
      map_zero (responseShearL2FamilyLinear
        (measurableSet_openCubeSet Q) σ hσ)
    simp [physicalProjectedCoefficient, physicalPositiveShear, hS]
  have hadd := physicalProjectedCoefficient_add Q σ hσ (-H) H
  rw [neg_add_cancel, hzero] at hadd
  have hadd' : physicalProjectedCoefficient Q σ hσ (-H) +
      physicalProjectedCoefficient Q σ hσ H = 0 := by
    simpa [physicalProjectedInsertion] using hadd.symm
  calc
    physicalProjectedCoefficient Q σ hσ (-H) =
        physicalProjectedCoefficient Q σ hσ (-H) +
          physicalProjectedCoefficient Q σ hσ H -
            physicalProjectedCoefficient Q σ hσ H := by abel
    _ = 0 - physicalProjectedCoefficient Q σ hσ H := by rw [hadd']
    _ = -physicalProjectedCoefficient Q σ hσ H := by abel

theorem physicalProjectedCoefficient_opNorm_le' (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q)) :
    ‖physicalProjectedCoefficient Q σ hσ H‖ ≤ ‖H‖ / σ := by
  let U := openCubeSet Q
  let first := hilbertPureFirstL2 U
  let second := hilbertSecondProjection U
  let flux := (physicalFluxSpace Q).toSubmodule
  let potential := (physicalPotentialSpace Q).toSubmodule
  have hfirst : ‖first‖ ≤ 1 := by
    dsimp [first, hilbertPureFirstL2]
    calc
      ‖pureFirst.toContinuousLinearMap.compLpL 2 (volumeMeasureOn U)‖ ≤
          ‖pureFirst.toContinuousLinearMap‖ :=
            ContinuousLinearMap.norm_compLpL_le _
      _ = 1 := by simp
  have hsecondVec : ‖hilbertBlockSecondProjectionVec‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [hilbertBlockSecondProjectionVec] using PiLp.norm_apply_le z 1
  have hsecond : ‖second‖ ≤ 1 := by
    dsimp [second, hilbertSecondProjection]
    calc
      ‖hilbertBlockSecondProjectionVec.compLpL 2 (volumeMeasureOn U)‖ ≤
          ‖hilbertBlockSecondProjectionVec‖ :=
            ContinuousLinearMap.norm_compLpL_le _
      _ ≤ 1 := hsecondVec
  have hfluxProj : ‖flux.orthogonalProjectionOnto‖ ≤ 1 :=
    flux.orthogonalProjectionOnto_norm_le
  have hfluxSub : ‖flux.subtypeL‖ ≤ 1 := flux.norm_subtypeL_le
  have hpotSub : ‖potential.subtypeL‖ ≤ 1 := potential.norm_subtypeL_le
  have hshear : ‖responseShearL2Operator σ hσ H‖ ≤ ‖H‖ / σ :=
    responseShearL2Operator_opNorm_le σ hσ H
  have hpositive : ‖physicalPositiveShear Q σ hσ H‖ ≤ ‖H‖ / σ := by
    unfold physicalPositiveShear
    change ‖-(hilbertSecondProjection U).comp
      ((responseShearL2Operator σ hσ H).comp
        (hilbertPureFirstL2 U))‖ ≤ ‖H‖ / σ
    calc
      ‖-(second.comp ((responseShearL2Operator σ hσ H).comp first))‖ =
          ‖second.comp ((responseShearL2Operator σ hσ H).comp first)‖ := norm_neg _
      _ ≤ ‖second‖ * ‖(responseShearL2Operator σ hσ H).comp first‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖second‖ *
          (‖responseShearL2Operator σ hσ H‖ * ‖first‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖H‖ / σ := by
        calc
          ‖second‖ *
              (‖responseShearL2Operator σ hσ H‖ * ‖first‖) ≤
            1 * ((‖H‖ / σ) * 1) := by
              gcongr
          _ = ‖H‖ / σ := by ring
  unfold physicalProjectedCoefficient
  change ‖(flux.subtypeL.comp flux.orthogonalProjectionOnto).comp
      ((physicalPositiveShear Q σ hσ H).comp potential.subtypeL)‖ ≤ ‖H‖ / σ
  calc
    ‖(flux.subtypeL.comp flux.orthogonalProjectionOnto).comp
        ((physicalPositiveShear Q σ hσ H).comp potential.subtypeL)‖ ≤
      ‖(flux.subtypeL.comp flux.orthogonalProjectionOnto)‖ *
        ‖(physicalPositiveShear Q σ hσ H).comp potential.subtypeL‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖flux.subtypeL‖ * ‖flux.orthogonalProjectionOnto‖) *
        (‖physicalPositiveShear Q σ hσ H‖ * ‖potential.subtypeL‖) := by
          gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖H‖ / σ := by
      calc
        (‖flux.subtypeL‖ * ‖flux.orthogonalProjectionOnto‖) *
            (‖physicalPositiveShear Q σ hσ H‖ * ‖potential.subtypeL‖) ≤
          (1 * 1) * ((‖H‖ / σ) * 1) := by gcongr
        _ = ‖H‖ / σ := by ring

theorem pureFluxBlockOperator_inserted_neg' {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (D : X →L[ℝ] Y) :
    pureFluxBlockOperator 0 (-D) = -pureFluxBlockOperator 0 D := by
  ext z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ Y X).injective
  change (pureFluxBlockOperator 0 (-D) z).ofLp =
    (-pureFluxBlockOperator 0 D z).ofLp
  simp [pureFluxBlockOperator_apply]

theorem physicalParity_observables_continuous'
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (e : Vec 2) :
    Continuous (physicalParityLinearObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityHessianObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityCubicObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityQuarticObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityResponseIncrement Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) := by
  let U := openCubeSet Q
  let R := physicalResponseRestriction Q hQ
  let A := physicalParityCoefficient Q σ hσ R
  let α := ν / σ
  let hα : 0 < α := div_pos hν hσ
  let B := physicalParityOldInverse Q ν σ hν hσ R
  let C := physicalParityInsertionBlock Q σ hσ R
  let N : C(K, ℝ) → C(K, ℝ) → physicalParityHilbert Q →L[ℝ]
      physicalParityHilbert Q := fun x y =>
    pureFluxBlockInverse α hα (A x + A y)
  let J := pureFluxParity (Y := HilbertVectorL2 U)
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : pureFluxPair (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    pureFluxLoad (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  let linear : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityLinearObservable Q ν σ hν hσ R e
  let hessian : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityHessianObservable Q ν σ hν hσ R e
  let cubic : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityCubicObservable Q ν σ hν hσ R e
  let quartic : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityQuarticObservable Q ν σ hν hσ R e
  let responseIncrement : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityResponseIncrement Q ν σ hν hσ R e
  let Acont : C(K, ℝ) → (physicalPotentialSpace Q).toSubmodule →L[ℝ]
      HilbertVectorL2 U := fun x => A x
  have hAcont : Continuous Acont := by
    change Continuous (fun x =>
      physicalProjectedCoefficient Q σ hσ (R x))
    exact (physicalProjectedCoefficient_continuous' Q σ hσ).comp R.continuous
  have hAadd (x y : C(K, ℝ)) : Acont x + Acont y = Acont (x + y) := by
    change physicalProjectedCoefficient Q σ hσ (R x) +
        physicalProjectedCoefficient Q σ hσ (R y) =
      physicalProjectedCoefficient Q σ hσ (R (x + y))
    rw [R.map_add]
    simpa [physicalProjectedInsertion] using
      (physicalProjectedCoefficient_add Q σ hσ (R x) (R y)).symm
  have hAprod : Continuous (fun p : C(K, ℝ) × C(K, ℝ) => A p.1 + A p.2) := by
    have hEq : (fun p : C(K, ℝ) × C(K, ℝ) => A p.1 + A p.2) =
        fun p => A (p.1 + p.2) := by
      funext p
      exact hAadd p.1 p.2
    rw [hEq]
    exact hAcont.comp (continuous_fst.add continuous_snd)
  have hBcont : Continuous (fun x : C(K, ℝ) => B x) := by
    change Continuous (fun x =>
      pureFluxBlockInverse α hα (Acont x))
    exact (pureFluxBlockInverse_continuous' hα).comp hAcont
  have hCcont : Continuous (fun y : C(K, ℝ) => C y) := by
    change Continuous (fun y =>
      pureFluxBlockOperator 0 (Acont y))
    exact (pureFluxBlockInserted_continuous').comp hAcont
  have hNcont : Continuous (fun p : C(K, ℝ) × C(K, ℝ) => N p.1 p.2) := by
    have hNcont' : Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
        pureFluxBlockInverse α hα (A p.1 + A p.2)) :=
      (pureFluxBlockInverse_continuous' hα).comp hAprod
    exact hNcont'
  have hlinearCont : Continuous linear := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1LinearTerm (B p.1) J f (C p.2))
    fun_prop [hilbertG1LinearTerm]
  have hhessianCont : Continuous hessian := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1HessianTerm (B p.1) J f (C p.2))
    fun_prop [hilbertG1HessianTerm]
  have hcubicCont : Continuous cubic := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1CubicTerm (B p.1) J f (C p.2))
    fun_prop [hilbertG1CubicTerm]
  have hquarticCont : Continuous quartic := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1QuarticTerm (B p.1) J f (C p.2) (N p.1 p.2))
    fun_prop [hilbertG1QuarticTerm]
  have hRespObservable : Continuous
      (responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e)) :=
    (responseFrameEnergyObservable_contDiff
      (measurableSet_openCubeSet Q)
      (by
        rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
        exact cubeVolume_pos Q)
      ν σ hν hσ (0, e)).continuous
  have hrespCont : Continuous responseIncrement := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) (R (p.1 + p.2)) -
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) (R p.1))
    exact (hRespObservable.comp (R.continuous.comp
      (continuous_fst.add continuous_snd))).sub
      (hRespObservable.comp (R.continuous.comp continuous_fst))
  exact ⟨hlinearCont, hhessianCont, hcubicCont, hquarticCont, hrespCont⟩

theorem physicalParity_insertion_neg'
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (y : C(K, ℝ)) :
    physicalParityInsertionBlock Q σ hσ R (-y) =
      -physicalParityInsertionBlock Q σ hσ R y := by
  let A := physicalParityCoefficient Q σ hσ R
  have hAneg : A (-y) = -A y := by
    change physicalProjectedCoefficient Q σ hσ (R (-y)) =
      -physicalProjectedCoefficient Q σ hσ (R y)
    rw [map_neg]
    exact physicalProjectedCoefficient_neg' Q σ hσ (R y)
  change pureFluxBlockOperator 0 (A (-y)) =
    -pureFluxBlockOperator 0 (A y)
  rw [hAneg]
  exact pureFluxBlockOperator_inserted_neg' (A y)

theorem physicalParity_fresh_fourth_integrable'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {K : Set (Vec 2)} [CompactSpace K] (m : ℤ) :
    Integrable (fun z : C(K, ℝ) => (1 + ‖z‖) ^ 4)
      (physicalParityFreshMarginal M m) := by
  obtain ⟨T, v, hv, hlaw⟩ :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM m (K := K)
  have hSeriesLp : MemLp (gaussianSeriesLimitE hv T) ((6 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := by
    convert memLp_gaussianSeriesLimitE hv T (p := (6 : ℝ)) (by norm_num) using 1;
    norm_num
  have hGaussianFourth : Integrable
      (fun z : C(K, ℝ) => (1 + ‖z‖) ^ 4)
      (standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T)) := by
    apply (integrable_map_measure (by fun_prop)
      (stronglyMeasurable_gaussianSeriesLimitE hv T).measurable.aemeasurable).mpr
    change Integrable
      (fun ω : ℕ → ℝ => (1 + ‖gaussianSeriesLimitE hv T ω‖) ^ 4)
      standardGaussianInfinitePi
    exact integrable_one_add_norm_pow_of_memLp (d := 4) hSeriesLp
  have hMarginal : physicalParityFreshMarginal M m =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T) := by
    change (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 (m + 1))) = _
    exact hlaw
  rw [hMarginal]
  exact hGaussianFourth

theorem physicalParity_response_pointwise'
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (x y : C(K, ℝ)) :
    physicalParityResponseIncrement Q ν σ hν hσ R e (x, y) =
      (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        (physicalParityLinearObservable Q ν σ hν hσ R e (x, y) +
          physicalParityHessianObservable Q ν σ hν hσ R e (x, y) +
          physicalParityCubicObservable Q ν σ hν hσ R e (x, y) +
          physicalParityQuarticObservable Q ν σ hν hσ R e (x, y)) := by
  have h := physicalResponse_fourTerm_identity Q ν σ hν hσ (R x) (R y) e
  have hR : R (x + y) = R x + R y := R.map_add x y
  rw [physicalParityResponseIncrement, hR]
  simp [physicalParityLinearObservable,
    physicalParityHessianObservable, physicalParityCubicObservable,
    physicalParityQuarticObservable, physicalParityCoefficient,
    physicalConstantLoad,
    physicalProjectedInsertion, hilbertG1LinearTerm,
    hilbertG1HessianTerm, hilbertG1CubicTerm, hilbertG1QuarticTerm] at h ⊢
  linarith

end

end ASDExplicitGamma.Scalar
