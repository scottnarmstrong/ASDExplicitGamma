module

public import ASDExplicitGamma.Response.ResponseRealization
public import ASDExplicitGamma.Gaussian.SeriesHeat
public import ASDExplicitGamma.Variational.TraceDefect
public import Homogenization.CoarseGraining.MuOperator.AEEOperator.CanonicalCubeSet
public import Homogenization.CoarseGraining.CoarseBounds.AeBridge

@[expose] public section

namespace ASDExplicitGamma.Response

open Homogenization
open ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian

noncomputable section

private theorem response_fderiv_translate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ} (x y : E)
    (hΦ : DifferentiableAt ℝ Φ (x + y)) :
    fderiv ℝ (fun z => Φ (x + z)) y = fderiv ℝ Φ (x + y) := by
  have hinner : HasFDerivAt (fun z : E => x + z)
      (ContinuousLinearMap.id ℝ E) y := (hasFDerivAt_id y).const_add x
  have hcomp := hΦ.hasFDerivAt.comp y hinner
  have hderiv := hcomp.fderiv
  simpa [Function.comp_def] using hderiv

private theorem response_second_fderiv_translate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (x y u w : E) :
    fderiv ℝ (fun z => fderiv ℝ Φ (x + z) w) y u =
      fderiv ℝ (fun z => fderiv ℝ Φ z w) (x + y) u := by
  have hFderiv : ContDiffAt ℝ 1 (fderiv ℝ Φ) (x + y) :=
    hΦ.contDiffAt.fderiv_right (by norm_num)
  have hDirectional : ContDiffAt ℝ 1
      (fun z => fderiv ℝ Φ z w) (x + y) := by
    exact hFderiv.clm_apply contDiffAt_const
  have htranslate := response_fderiv_translate
    (Φ := fun z => fderiv ℝ Φ z w) x y
    (hDirectional.differentiableAt (by norm_num))
  exact congrArg (fun L : E →L[ℝ] ℝ => L u) htranslate

/-- The doubled coefficient response in the fixed frame, indexed by the physical
bounded skew field. -/
noncomputable def responseFrameEnergyObservable {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) :
    ResponseCoefficient U → ℝ :=
  fun k => responseFrameEnergy hU hvol ν σ hν hσ 0 P k

/-- The full coefficient-indexed response is the linear-family minimum on
the single frame-energy Hilbert space frozen at coefficient zero. -/
theorem responseFrameEnergyObservable_eq_linearShearMinimum
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P =
      fun k => linearShearMinimum
        (responseFrameEnergyVariationSpace hU hvol ν σ hν hσ 0)
        (responseFrameEnergyShearFamily hU hvol ν σ hν hσ 0)
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ 0 P) k
        (responseFrameEnergyShearFamily_pairwise_nilpotent
          hU hvol ν σ hν hσ 0) := by
  funext k
  simpa [responseFrameEnergyObservable] using
    responseFrameEnergy_eq_linearShearMinimum
      hU hvol ν σ hν hσ 0 P k

theorem responseFrameEnergyObservable_contDiff
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) :
    ContDiff ℝ 2 (responseFrameEnergyObservable hU hvol ν σ hν hσ P) := by
  rw [responseFrameEnergyObservable_eq_linearShearMinimum]
  exact linearShearMinimum_contDiff
    (responseFrameEnergyVariationSpace hU hvol ν σ hν hσ 0)
    (responseFrameEnergyShearFamily hU hvol ν σ hν hσ 0)
    (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ 0 P)
    (responseFrameEnergyShearFamily_pairwise_nilpotent
      hU hvol ν σ hν hσ 0)

private theorem responseFrameEnergyBaseMinimizer_orthogonal
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) :
    ∀ Y : (responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k).toSubmodule,
      inner ℝ (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P) Y = 0 := by
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let D := responseEnergyHilbertData
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)
  change ∀ Y : (responseEnergyCorrectionSpace M D).toSubmodule,
      inner ℝ (responseEnergyUp D (M.minimizerMap P)) Y = 0
  intro Y
  exact responseEnergyMinimizer_orthogonal M P Y

private theorem responseFrameEnergyObservable_local_eq
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k : ResponseCoefficient U) :
    (fun H => responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + H)) =
      fun H => linearShearMinimum
        (responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k)
        (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k)
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P) H
        (responseFrameEnergyShearFamily_pairwise_nilpotent
          hU hvol ν σ hν hσ k) := by
  funext H
  calc
    responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + H) =
        responseFrameEnergy hU hvol ν σ hν hσ k P H := by
      change responseFrameEnergy hU hvol ν σ hν hσ 0 P (k + H) =
        responseFrameEnergy hU hvol ν σ hν hσ k P H
      change 2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
          (0 + (k + H))).toMuHilbertRealization.muCandidate P =
        2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
          (k + H)).toMuHilbertRealization.muCandidate P
      rw [zero_add]
    _ = _ := responseFrameEnergy_eq_linearShearMinimum
      hU hvol ν σ hν hσ k P H

/-- First derivative formula at every physical coefficient. -/
theorem responseFrameEnergyObservable_fderiv
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k H =
      2 * inner ℝ
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)
        (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H
          (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)) := by
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k
  have hCont := responseFrameEnergyObservable_contDiff hU hvol ν σ hν hσ P
  have hDiff : DifferentiableAt ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k :=
    (hCont.differentiable (by norm_num)).differentiableAt
  have hDiff' : DifferentiableAt ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) (k + 0) := by
    simpa only [add_zero] using hDiff
  have hTrans := response_fderiv_translate
    (Φ := responseFrameEnergyObservable hU hvol ν σ hν hσ P) k 0
    hDiff'
  have hTrans' : fderiv ℝ
      (fun z => responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + z)) 0 =
        fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k := by
    simpa only [add_zero] using hTrans
  have hLocal := responseFrameEnergyObservable_local_eq hU hvol ν σ hν hσ P k
  calc
    fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k H =
        fderiv ℝ (fun z => responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + z)) 0 H := by
      exact congrArg (fun L : ResponseCoefficient U →L[ℝ] ℝ => L H) hTrans'.symm
    _ = fderiv ℝ (fun z => linearShearMinimum V C S z hNil) 0 H := by
      rw [hLocal]
    _ = 2 * inner ℝ S (C H S) := by
      change fderiv ℝ (fun h => linearShearMinimum V C S h hNil) 0 H = _
      exact linearShearMinimum_fderiv_zero V C S hNil
        (responseFrameEnergyBaseMinimizer_orthogonal hU hvol ν σ hν hσ k P) H

/-- Bilinear Hessian formula at every physical coefficient. -/
theorem responseFrameEnergyObservable_hessian
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H K : ResponseCoefficient U) :
    fderiv ℝ (fun z => fderiv ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z K) k H =
      2 * inner ℝ
          (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H
            (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P))
          (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k K
            (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)) -
        2 * inner ℝ
          ((responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k).toSubmodule.orthogonalProjectionOnto
            (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H
              (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P) +
             responseAdjointMap (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H)
              (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)) :
            EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k))
          ((responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k).toSubmodule.orthogonalProjectionOnto
            (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k K
              (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P) +
             responseAdjointMap (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k K)
              (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)) :
            EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k)) := by
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k
  have hCont := responseFrameEnergyObservable_contDiff hU hvol ν σ hν hσ P
  have hLocal := responseFrameEnergyObservable_local_eq hU hvol ν σ hν hσ P k
  have hTranslate := response_second_fderiv_translate hCont k 0 H K
  have hGradShift :
      (fun z => fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P)
        (k + z) K) =
      (fun z => fderiv ℝ
        (fun H => responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + H)) z K) := by
    funext z
    have hDiff : DifferentiableAt ℝ
        (responseFrameEnergyObservable hU hvol ν σ hν hσ P) (k + z) :=
      (hCont.differentiable (by norm_num)).differentiableAt
    exact congrArg (fun L : ResponseCoefficient U →L[ℝ] ℝ => L K)
      (response_fderiv_translate
        (Φ := responseFrameEnergyObservable hU hvol ν σ hν hσ P) k z hDiff).symm
  have hGradLocal :
      (fun z => fderiv ℝ
        (fun H => responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + H)) z K) =
      (fun z => fderiv ℝ (fun H => linearShearMinimum V C S H hNil) z K) := by
    exact congrArg (fun F : ResponseCoefficient U → ℝ =>
      fun z => fderiv ℝ F z K) hLocal
  calc
    fderiv ℝ (fun z => fderiv ℝ
        (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z K) k H =
        fderiv ℝ (fun z => fderiv ℝ
          (responseFrameEnergyObservable hU hvol ν σ hν hσ P) (k + z) K) 0 H := by
      simpa only [add_zero] using hTranslate.symm
    _ = fderiv ℝ (fun z => fderiv ℝ
          (fun H => responseFrameEnergyObservable hU hvol ν σ hν hσ P (k + H)) z K) 0 H := by
      exact congrArg (fun F : ResponseCoefficient U → ℝ => fderiv ℝ F 0 H) hGradShift
    _ = fderiv ℝ (fun z => fderiv ℝ (fun H =>
        linearShearMinimum V C S H hNil) z K) 0 H := by
      exact congrArg (fun F : ResponseCoefficient U → ℝ => fderiv ℝ F 0 H) hGradLocal
    _ = 2 * inner ℝ (C H S) (C K S) - 2 * inner ℝ
        (V.toSubmodule.orthogonalProjectionOnto
          (C H S + responseAdjointMap (C H) S))
        (V.toSubmodule.orthogonalProjectionOnto
          (C K S + responseAdjointMap (C K) S)) :=
      linearShearMinimum_second_fderiv_zero V C S hNil
        (responseFrameEnergyBaseMinimizer_orthogonal hU hvol ν σ hν hσ k P) H K

private theorem responseFrameEnergyBaseMinimizer_norm_sq
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) :
    ‖responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P‖ ^ 2 =
      responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let : NormedAddCommGroup (EnergyCarrier D) :=
    instNormedAddCommGroupEnergyCarrier D
  let : InnerProductSpace ℝ (EnergyCarrier D) :=
    instInnerProductSpaceEnergyCarrier D
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k
  have hOrth := responseFrameEnergyBaseMinimizer_orthogonal hU hvol ν σ hν hσ k P
  calc
    ‖S‖ ^ 2 = linearShearMinimum V C S 0 hNil :=
      (linearShearMinimum_zero_eq_norm_sq V C S hNil hOrth).symm
    _ = responseFrameEnergy hU hvol ν σ hν hσ k P 0 :=
      (responseFrameEnergy_eq_linearShearMinimum hU hvol ν σ hν hσ k P 0).symm
    _ = responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
      change 2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
          (k + 0)).toMuHilbertRealization.muCandidate P =
        2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
          (0 + k)).toMuHilbertRealization.muCandidate P
      rw [add_zero, zero_add]

private theorem responseFrameEnergyObservable_value_le
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k : ResponseCoefficient U) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k ≤
      (1 + ‖k‖ / ν) ^ 2 *
        responseFrameEnergyObservable hU hvol ν σ hν hσ P 0 := by
  let M := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ 0
  let D := responseEnergyHilbertData M.toMuHilbertRealization
  let V := responseEnergyCorrectionSpace M.toMuHilbertRealization D
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ 0
  let S := responseEnergyUp D (M.toMuHilbertRealization.minimizerMap P)
  let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ 0
  let : NormedAddCommGroup (EnergyCarrier D) :=
    instNormedAddCommGroupEnergyCarrier D
  let : InnerProductSpace ℝ (EnergyCarrier D) :=
    instInnerProductSpaceEnergyCarrier D
  have hTrial := linearShearMinimum_minimizes V C S S k hNil
    (by simp : S - S ∈ V.toSubmodule)
  have hPoint : ‖C k S‖ ≤ (‖k‖ / ν) * ‖S‖ := by
    have h := responseFrameEnergyShearFamily_apply_norm_le
      hU hvol ν σ hν hσ 0 k S
    change ‖responseEnergyShearFamilyLinear hU σ hσ D k S‖ ≤ _
    exact h
  have hMap : nilpotentShearMap (C k) 1 S = S + C k S := by
    simp [nilpotentShearMap]
  have hNorm : ‖nilpotentShearMap (C k) 1 S‖ ≤
      (1 + ‖k‖ / ν) * ‖S‖ := by
    rw [hMap]
    calc
      ‖S + C k S‖ ≤ ‖S‖ + ‖C k S‖ := norm_add_le _ _
      _ ≤ ‖S‖ + (‖k‖ / ν) * ‖S‖ := add_le_add (le_refl _) hPoint
      _ = (1 + ‖k‖ / ν) * ‖S‖ := by ring
  have hObs : responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      linearShearMinimum V C S k hNil := by
    exact congrFun (responseFrameEnergyObservable_eq_linearShearMinimum
      hU hvol ν σ hν hσ P) k
  rw [hObs]
  have hSq : linearShearMinimum V C S k hNil ≤
      ((1 + ‖k‖ / ν) * ‖S‖) ^ 2 := by
    calc
      linearShearMinimum V C S k hNil ≤ ‖nilpotentShearMap (C k) 1 S‖ ^ 2 := hTrial
      _ ≤ ((1 + ‖k‖ / ν) * ‖S‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hNorm
  have hSsq : ‖S‖ ^ 2 = responseFrameEnergyObservable hU hvol ν σ hν hσ P 0 := by
    change ‖responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ 0 P‖ ^ 2 = _
    exact responseFrameEnergyBaseMinimizer_norm_sq hU hvol ν σ hν hσ 0 P
  calc
    linearShearMinimum V C S k hNil ≤ ((1 + ‖k‖ / ν) * ‖S‖) ^ 2 := hSq
    _ = (1 + ‖k‖ / ν) ^ 2 *
        responseFrameEnergyObservable hU hvol ν σ hν hσ P 0 := by
      rw [mul_pow, hSsq]

private theorem responseFrameEnergyObservable_fderiv_norm_le
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k : ResponseCoefficient U) :
    ‖fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k‖ ≤
      (2 / ν) * responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
  let D := responseEnergyHilbertData
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)
  let : NormedAddCommGroup (EnergyCarrier D) :=
    instNormedAddCommGroupEnergyCarrier D
  let : InnerProductSpace ℝ (EnergyCarrier D) :=
    instInnerProductSpaceEnergyCarrier D
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  have hSsq := responseFrameEnergyBaseMinimizer_norm_sq hU hvol ν σ hν hσ k P
  have hBound (H : ResponseCoefficient U) :
      ‖fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k H‖ ≤
        (2 / ν) * ‖S‖ ^ 2 * ‖H‖ := by
    rw [responseFrameEnergyObservable_fderiv]
    have hCH : ‖C H S‖ ≤ (‖H‖ / ν) * ‖S‖ := by
      have h := responseFrameEnergyShearFamily_apply_norm_le
        hU hvol ν σ hν hσ k H S
      change ‖responseEnergyShearFamilyLinear hU σ hσ D H S‖ ≤ _
      exact h
    rw [Real.norm_eq_abs]
    calc
      |2 * inner ℝ S (C H S)| = 2 * |inner ℝ S (C H S)| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      _ ≤ 2 * (‖S‖ * ‖C H S‖) := by
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ 2 * (‖S‖ * ((‖H‖ / ν) * ‖S‖)) := by
        gcongr
      _ = (2 / ν) * ‖S‖ ^ 2 * ‖H‖ := by
        field_simp [hν.ne']
  have hCoeff : 0 ≤ (2 / ν) * ‖S‖ ^ 2 := by positivity
  have hOp := ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k)
    hCoeff hBound
  calc
    ‖fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k‖ ≤
        (2 / ν) * ‖S‖ ^ 2 := hOp
    _ = (2 / ν) * responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
      rw [hSsq]

private theorem responseFrameEnergyObservable_second_fderiv_norm_le
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H K : ResponseCoefficient U) :
    |fderiv ℝ (fun z => fderiv ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z K) k H| ≤
      (10 / ν ^ 2) * responseFrameEnergyObservable hU hvol ν σ hν hσ P k *
        ‖H‖ * ‖K‖ := by
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let D := responseEnergyHilbertData
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)
  let : NormedAddCommGroup (EnergyCarrier D) :=
    instNormedAddCommGroupEnergyCarrier D
  let : InnerProductSpace ℝ (EnergyCarrier D) :=
    instInnerProductSpaceEnergyCarrier D
  have hSsq : ‖S‖ ^ 2 = responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
    simpa [S] using responseFrameEnergyBaseMinimizer_norm_sq
      hU hvol ν σ hν hσ k P
  have hPoint (L : ResponseCoefficient U) (z : EnergyCarrier D) :
      ‖C L z‖ ≤ (‖L‖ / ν) * ‖z‖ := by
    have h := responseFrameEnergyShearFamily_apply_norm_le
      hU hvol ν σ hν hσ k L z
    simpa [C, responseFrameEnergyShearFamily] using h
  have hOp (L : ResponseCoefficient U) : ‖C L‖ ≤ ‖L‖ / ν := by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hν.le) ?_
    intro z
    calc
      ‖C L z‖ ≤ (‖L‖ / ν) * ‖z‖ := hPoint L z
      _ = (‖L‖ / ν) * ‖z‖ := rfl
  have hCHS : ‖C H S‖ ≤ (‖H‖ / ν) * ‖S‖ := hPoint H S
  have hCKS : ‖C K S‖ ≤ (‖K‖ / ν) * ‖S‖ := hPoint K S
  have hAdjH : ‖responseAdjointMap (C H) S‖ ≤ (‖H‖ / ν) * ‖S‖ := by
    change ‖(C H).adjoint S‖ ≤ (‖H‖ / ν) * ‖S‖
    calc
      ‖(C H).adjoint S‖ ≤ ‖(C H).adjoint‖ * ‖S‖ := (C H).adjoint.le_opNorm S
      _ = ‖C H‖ * ‖S‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ (‖H‖ / ν) * ‖S‖ := by gcongr; exact hOp H
  have hAdjK : ‖responseAdjointMap (C K) S‖ ≤ (‖K‖ / ν) * ‖S‖ := by
    change ‖(C K).adjoint S‖ ≤ (‖K‖ / ν) * ‖S‖
    calc
      ‖(C K).adjoint S‖ ≤ ‖(C K).adjoint‖ * ‖S‖ := (C K).adjoint.le_opNorm S
      _ = ‖C K‖ * ‖S‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ (‖K‖ / ν) * ‖S‖ := by gcongr; exact hOp K
  let pH := V.toSubmodule.orthogonalProjectionOnto
    (C H S + responseAdjointMap (C H) S)
  let pK := V.toSubmodule.orthogonalProjectionOnto
    (C K S + responseAdjointMap (C K) S)
  let a := (‖H‖ / ν) * ‖S‖
  let b := (‖K‖ / ν) * ‖S‖
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hpH : ‖pH‖ ≤ 2 * a := by
    dsimp [pH, a]
    calc
      _ ≤ ‖C H S + responseAdjointMap (C H) S‖ :=
        V.toSubmodule.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ ‖C H S‖ + ‖responseAdjointMap (C H) S‖ := norm_add_le _ _
      _ ≤ a + a := add_le_add hCHS hAdjH
      _ = 2 * a := by ring
  have hpK : ‖pK‖ ≤ 2 * b := by
    dsimp [pK, b]
    calc
      _ ≤ ‖C K S + responseAdjointMap (C K) S‖ :=
        V.toSubmodule.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ ‖C K S‖ + ‖responseAdjointMap (C K) S‖ := norm_add_le _ _
      _ ≤ b + b := add_le_add hCKS hAdjK
      _ = 2 * b := by ring
  have hinner₁ : |2 * inner ℝ (C H S) (C K S)| ≤ 2 * a * b := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      2 * |inner ℝ (C H S) (C K S)| ≤
          2 * (‖C H S‖ * ‖C K S‖) := by
            gcongr
            exact abs_real_inner_le_norm _ _
      _ ≤ 2 * (a * b) := by gcongr
      _ = 2 * a * b := by ring
  have hinner₂ : |2 * inner ℝ pH pK| ≤ 8 * a * b := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      2 * |inner ℝ pH pK| ≤ 2 * (‖pH‖ * ‖pK‖) := by
        gcongr
        exact abs_real_inner_le_norm _ _
      _ ≤ 2 * ((2 * a) * (2 * b)) := by gcongr
      _ = 8 * a * b := by ring
  have hBase : |fderiv ℝ (fun z => fderiv ℝ
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z K) k H| ≤
      10 * a * b := by
    rw [responseFrameEnergyObservable_hessian]
    calc
      |2 * inner ℝ (C H S) (C K S) - 2 * inner ℝ pH pK| ≤
          |2 * inner ℝ (C H S) (C K S)| + |2 * inner ℝ pH pK| := abs_sub _ _
      _ ≤ 2 * a * b + 8 * a * b := add_le_add hinner₁ hinner₂
      _ = 10 * a * b := by ring
  calc
    |fderiv ℝ (fun z => fderiv ℝ
        (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z K) k H| ≤ 10 * a * b := hBase
    _ = (10 / ν ^ 2) * ‖S‖ ^ 2 * ‖H‖ * ‖K‖ := by
      dsimp [a, b]
      field_simp [hν.ne']
    _ = (10 / ν ^ 2) * responseFrameEnergyObservable hU hvol ν σ hν hσ P k *
        ‖H‖ * ‖K‖ := by rw [hSsq]

private theorem response_muHilbertRealization_ext
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuHilbertRealization U a)
    (hc : M.correctionSpace = N.correctionSpace)
    (hl : M.constantField = N.constantField)
    (he : M.energyBilin = N.energyBilin) : M = N := by
  cases M with
  | mk cm lm em sm cm' =>
    cases N with
    | mk cn ln en sn cn' =>
      simp only [MuHilbertRealization.mk.injEq]
      exact ⟨by simpa using hc, by simpa using hl, by simpa using he⟩

private theorem response_muCandidate_eq_of_hilbert_fields
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuHilbertRealization U a)
    (hc : M.correctionSpace = N.correctionSpace)
    (hl : M.constantField = N.constantField)
    (he : M.energyBilin = N.energyBilin) (P : BlockVec 2) :
    M.muCandidate P = N.muCandidate P := by
  exact congrArg (fun R : MuHilbertRealization U a => R.muCandidate P)
    (response_muHilbertRealization_ext M N hc hl he)

private theorem response_muOperatorRealization_operator_eq
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuOperatorRealization U a)
    (h : ∀ F : HilbertBlockL2 U, M.operator F =ᵐ[volumeMeasureOn U] N.operator F) :
    M.operator = N.operator := by
  ext F
  exact h F

private theorem response_deterministic_operator_eq_canonicalAEE
    {Q : TriadicCube 2} {j : ℕ}
    (aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a})
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) aSlice.1) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuOperatorRealization.operator =
    (canonicalAEEMuOperatorSystemData Q j aSlice).toMuOperatorRealization.operator := by
  let M : MuOperatorSystemData (cubeSet Q) aSlice.1 :=
    PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)
  let N : AEEMuOperatorSystemData (cubeSet Q) aSlice.1 :=
    canonicalAEEMuOperatorSystemData Q j aSlice
  change M.toMuOperatorRealization.operator = N.toMuOperatorRealization.operator
  apply response_muOperatorRealization_operator_eq
    M.toMuOperatorRealization N.toMuOperatorRealization
  intro F
  filter_upwards [
    M.toMuOperatorRealization.ae_apply F,
    N.toMuOperatorRealization.ae_apply F]
    with x hdet haee
  rw [hdet, haee]

private theorem response_deterministic_correctionSpace_eq_canonicalAEE
    {Q : TriadicCube 2} {j : ℕ}
    (aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a})
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) aSlice.1) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuHilbertRealization.correctionSpace =
    (canonicalAEEMuOperatorSystemData Q j aSlice).toMuHilbertRealization.correctionSpace := by
  simp only [PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn,
    PotentialSolenoidalL2Data.correctionSpace_toMuOperatorSystemData,
    MuOperatorSystemData.toMuHilbertRealization,
    MuOperatorSystemData.toMuOperatorRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
    AEEMuOperatorSystemData.toMuHilbertRealization,
    AEEMuOperatorSystemData.toMuOperatorRealization,
    correctionSpace_canonicalAEEMuOperatorSystemData,
    canonicalAEEMuCorrectionSpaceData, canonicalAEEPotentialSolenoidalL2Data]

private theorem response_deterministic_constantField_eq_canonicalAEE
    {Q : TriadicCube 2} {j : ℕ}
    (aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a})
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) aSlice.1) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuHilbertRealization.constantField =
    (canonicalAEEMuOperatorSystemData Q j aSlice).toMuHilbertRealization.constantField := by
  simp only [PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn,
    PotentialSolenoidalL2Data.toMuOperatorSystemData,
    MuOperatorSystemData.toMuHilbertRealization,
    MuOperatorSystemData.toMuOperatorRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
    canonicalAEEMuOperatorSystemData, canonicalAEEMuCorrectionSpaceData,
    canonicalAEEPotentialSolenoidalL2Data, canonicalAEEMuCoeffOperatorData,
    AEEMuCoeffOperatorData.toMuOperatorRealization,
    AEEMuOperatorSystemData.toMuOperatorRealization,
    AEEMuOperatorSystemData.toMuHilbertRealization]

private theorem response_energyBilin_eq_of_operator_eq
    {U : Set (Vec 2)} {a : CoeffField 2}
    (M N : MuOperatorRealization U a) (h : M.operator = N.operator) :
    energyBilinOfOperator M.operator = energyBilinOfOperator N.operator := by
  rw [h]

private theorem response_deterministic_muCandidate_eq_mu_triCube
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (P : BlockVec 2) :
    (PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)).toMuHilbertRealization.muCandidate P =
      Mu (cubeSet Q) P a := by
  have hAEE := IsAEEllipticFieldOn.of_isEllipticFieldOn hEll
  obtain ⟨j, hj⟩ := AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hAEE
  let aSlice : {a : CoeffField 2 // AEEQuantitativeEllipticSlice (cubeSet Q) j a} :=
    ⟨a, hj⟩
  let Mdet : MuOperatorSystemData (cubeSet Q) a :=
    PotentialSolenoidalL2Data.toMuOperatorSystemDataOfIsEllipticFieldOn
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)) hEll
      (volume_cubeSet_toReal_pos Q)
  let Maee : AEEMuOperatorSystemData (cubeSet Q) a :=
    canonicalAEEMuOperatorSystemData Q j aSlice
  let Hdet := Mdet.toMuHilbertRealization
  let Haee := Maee.toMuHilbertRealization
  have hOp : Mdet.toMuOperatorRealization.operator =
      Maee.toMuOperatorRealization.operator := by
    exact response_deterministic_operator_eq_canonicalAEE aSlice hEll
  have hEnergy : Hdet.energyBilin = Haee.energyBilin := by
    change energyBilinOfOperator Mdet.toMuOperatorRealization.operator =
      energyBilinOfOperator Maee.toMuOperatorRealization.operator
    exact response_energyBilin_eq_of_operator_eq
      Mdet.toMuOperatorRealization Maee.toMuOperatorRealization hOp
  calc
    Hdet.muCandidate P = Haee.muCandidate P :=
      response_muCandidate_eq_of_hilbert_fields Hdet Haee
        (response_deterministic_correctionSpace_eq_canonicalAEE aSlice hEll)
        (response_deterministic_constantField_eq_canonicalAEE aSlice hEll)
        hEnergy P
    _ = Mu (cubeSet Q) P a :=
      (mu_eq_canonicalAEEMuCandidate Q j aSlice P).symm

private theorem responseFrameEnergyObservable_eq_twice_frameMuCandidate
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k : ResponseCoefficient U) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P := by
  simp only [responseFrameEnergyObservable, responseFrameEnergy]
  exact congrArg
    (fun z : ResponseCoefficient U =>
      2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ z).toMuHilbertRealization.muCandidate P)
    (zero_add k)

private theorem response_planarFrameCoefficient_eq_smul_unit
    {U : Set (Vec 2)} (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (x : Vec 2) (hx : x ∈ U) :
    responseFramePlanarCoefficientField ν σ k x =
      ((ν / σ) • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x := by
  unfold responseFramePlanarCoefficientField responsePlanarCoefficientField
  change responsePlanarCoefficient (ν / σ) (responseCoefficientExtension k x / σ) =
    (ν / σ) • responsePlanarCoefficient 1 (responseCoefficientExtension (ν⁻¹ • k) x)
  rw [responseCoefficientExtension_smul_on (ν⁻¹) k hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply, smul_eq_mul]
  <;> field_simp [hν.ne', hσ.ne']

private theorem response_planarCoefficientField_eq_smul_unit_on
    {U : Set (Vec 2)} (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient U) (x : Vec 2) (hx : x ∈ U) :
    responsePlanarCoefficientField ν k x =
      (ν • responsePlanarCoefficientField 1 (ν⁻¹ • k)) x := by
  unfold responsePlanarCoefficientField
  change responsePlanarCoefficient ν (responseCoefficientExtension k x) =
    ν • responsePlanarCoefficient 1 (responseCoefficientExtension (ν⁻¹ • k) x)
  rw [responseCoefficientExtension_smul_on (ν⁻¹) k hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply, smul_eq_mul]
  <;> field_simp [hν.ne']

private theorem response_coarseMatrix_frame_eq {m : ℤ}
    (hU : MeasurableSet (cubeSet (originCube 2 m)))
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (cubeSet (originCube 2 m))) :
    coarseBlockMatrix (cubeSet (originCube 2 m))
        (responseFramePlanarCoefficientField ν σ k) =
      frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m))
        (responsePlanarCoefficientField ν k)) := by
  let U := cubeSet (originCube 2 m)
  let a₁ := responsePlanarCoefficientField 1 (ν⁻¹ • k)
  have hEll₁ : IsEllipticFieldOn 1 (1 + ‖ν⁻¹ • k‖ ^ 2) U a₁ := by
    simpa using responsePlanarCoefficientField_isElliptic hU 1 (by norm_num) (ν⁻¹ • k)
  have hCoeffFrameOn (x : Vec 2) (hx : x ∈ U) :
      responseFramePlanarCoefficientField ν σ k x = ((ν / σ) • a₁) x :=
    response_planarFrameCoefficient_eq_smul_unit ν σ hν hσ k x hx
  have hCoeffPhysicalOn (x : Vec 2) (hx : x ∈ U) :
      responsePlanarCoefficientField ν k x = (ν • a₁) x :=
    response_planarCoefficientField_eq_smul_unit_on ν hν k x hx
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsν_sq : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt hν.le
  have hCoeffPhysical' : ∀ x ∈ U,
      responsePlanarCoefficientField ν k x = ((Real.sqrt ν) ^ 2 • a₁) x := by
    intro x hx
    rw [hsν_sq]
    exact hCoeffPhysicalOn x hx
  have hCoarsePhysical :
      coarseBlockMatrix U (responsePlanarCoefficientField ν k) =
        coarseMatrixRescale (Real.sqrt ν) (coarseBlockMatrix U a₁) := by
    have hAE : responsePlanarCoefficientField ν k =ᵐ[MeasureTheory.volume.restrict U]
        ((Real.sqrt ν) ^ 2 • a₁) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      exact hCoeffPhysical' x hx
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
    exact coarseBlockMatrix_sq_smul_triCube hEll₁ hsν
  have hsFrame : 0 < Real.sqrt (ν / σ) :=
    Real.sqrt_pos.2 (div_pos hν hσ)
  have hsFrame_sq : (Real.sqrt (ν / σ)) ^ 2 = ν / σ :=
    Real.sq_sqrt (div_nonneg hν.le hσ.le)
  have hCoeffFrame' : ∀ x ∈ U,
      responseFramePlanarCoefficientField ν σ k x =
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) x := by
    intro x hx
    rw [hsFrame_sq]
    exact hCoeffFrameOn x hx
  have hCoarseFrame :
      coarseBlockMatrix U (responseFramePlanarCoefficientField ν σ k) =
        coarseMatrixRescale (Real.sqrt (ν / σ)) (coarseBlockMatrix U a₁) := by
    have hAE : responseFramePlanarCoefficientField ν σ k =ᵐ[MeasureTheory.volume.restrict U]
        ((Real.sqrt (ν / σ)) ^ 2 • a₁) := by
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      exact hCoeffFrame' x hx
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
    exact coarseBlockMatrix_sq_smul_triCube hEll₁ hsFrame
  have hRescale :
      coarseMatrixRescale (Real.sqrt (ν / σ)) (coarseBlockMatrix U a₁) =
        frameMatrix σ (coarseMatrixRescale (Real.sqrt ν) (coarseBlockMatrix U a₁)) := by
    have hInvFrame : (Real.sqrt (ν / σ)) ^ (-2 : ℤ) = σ / ν := by
      rw [zpow_neg, zpow_ofNat, hsFrame_sq]
      field_simp [hν.ne', hσ.ne']
    have hInvν : (Real.sqrt ν) ^ (-2 : ℤ) = ν⁻¹ := by
      rw [zpow_neg, zpow_ofNat, hsν_sq]
    cases coarseBlockMatrix U a₁ with
    | mk ul ur ll lr =>
      have hUL : (Real.sqrt (ν / σ)) ^ 2 • ul =
          σ⁻¹ • ((Real.sqrt ν) ^ 2 • ul) := by
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul, hsFrame_sq, hsν_sq]
        ; field_simp [hν.ne', hσ.ne']
      have hLR : (Real.sqrt (ν / σ)) ^ (-2 : ℤ) • lr =
          σ • ((Real.sqrt ν) ^ (-2 : ℤ) • lr) := by
        ext i j
        simp [Matrix.smul_apply, smul_eq_mul, hInvFrame, hInvν]
        ; field_simp [hν.ne', hσ.ne']
      simp only [coarseMatrixRescale, frameMatrix, BlockMat.mk.injEq]
      exact ⟨hUL, trivial, trivial, hLR⟩
  rw [hCoarseFrame, hCoarsePhysical, hRescale]

private theorem responseFrameEnergyObservable_eq_frameCoarseQuadratic
    {m : ℤ} (hU : MeasurableSet (cubeSet (originCube 2 m)))
    (hvol : 0 < (MeasureTheory.volume (cubeSet (originCube 2 m))).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k : ResponseCoefficient (cubeSet (originCube 2 m))) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      blockVecDot P (blockMatVecMul
        (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m))
          (responsePlanarCoefficientField ν k))) P) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k
  have hMu := response_deterministic_muCandidate_eq_mu_triCube
    (Q := originCube 2 m) (div_pos hν hσ) hEll P
  have hCandidate :
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P =
        Mu (cubeSet (originCube 2 m)) P (responseFramePlanarCoefficientField ν σ k) := by
    simpa [responseFrameMuOperatorSystemData] using hMu
  calc
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
        2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P :=
          responseFrameEnergyObservable_eq_twice_frameMuCandidate hU hvol ν σ hν hσ P k
    _ =
        2 * Mu (cubeSet (originCube 2 m)) P
          (responseFramePlanarCoefficientField ν σ k) := by rw [hCandidate]
    _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (cubeSet (originCube 2 m))
            (responseFramePlanarCoefficientField ν σ k)) P) := by
          rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube
            (div_pos hν hσ) hEll P]
          ring
    _ = blockVecDot P (blockMatVecMul
          (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m))
            (responsePlanarCoefficientField ν k))) P) := by
          rw [response_coarseMatrix_frame_eq hU ν σ hν hσ k]

/-- The coefficient-indexed four-load response is exactly the framed
coarse-matrix trace defect on an origin cube. -/
theorem responseFrameEnergyObservable_fourLoad_eq_traceDefect
    (m : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (cubeSet (originCube 2 m))) :
    (∑ i : Fin 2,
      (responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
        (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
        (orthonormalFrameLoad i 1) k +
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
        (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
        (orthonormalFrameLoad i (-1)) k)) - 4 =
      traceDefect (cubeSet (originCube 2 m)) (responsePlanarCoefficientField ν k) σ := by
  let U := cubeSet (originCube 2 m)
  let a := responsePlanarCoefficientField ν k
  let A := coarseBlockMatrix U a
  have hPlus (i : Fin 2) :
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
        (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
        (orthonormalFrameLoad i 1) k =
        (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i +
          (A.upperRight i i + A.lowerLeft i i)) / 2 := by
    rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic
      (measurableSet_cubeSet (originCube 2 m))
      (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
      (orthonormalFrameLoad i 1) k]
    change blockVecDot (orthonormalFrameLoad i 1)
      (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i 1)) = _
    simpa using orthonormalFrameLoad_energy A σ i 1 (by norm_num)
  have hMinus (i : Fin 2) :
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
        (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
        (orthonormalFrameLoad i (-1)) k =
        (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i -
          (A.upperRight i i + A.lowerLeft i i)) / 2 := by
    rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic
      (measurableSet_cubeSet (originCube 2 m))
      (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
      (orthonormalFrameLoad i (-1)) k]
    change blockVecDot (orthonormalFrameLoad i (-1))
      (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i (-1))) = _
    convert orthonormalFrameLoad_energy A σ i (-1) (by norm_num) using 1; ring
  have hLoadSum :
      (∑ i : Fin 2,
        (responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
          (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
          (orthonormalFrameLoad i 1) k +
        responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
          (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
          (orthonormalFrameLoad i (-1)) k)) =
      (∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hPlus i, hMinus i]
    ring
  have hSum :
      (∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i)) =
        σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ i : Fin 2,
      (responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
        (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
        (orthonormalFrameLoad i 1) k +
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 m))
        (volume_cubeSet_toReal_pos (originCube 2 m)) ν σ hν hσ
        (orthonormalFrameLoad i (-1)) k)) - 4 =
        (∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i)) - 4 := by
          rw [hLoadSum]
    _ = traceDefect U a σ := by
          rw [hSum]
          rfl

/-- The coefficient-indexed response has the polynomial C² bounds required
by the Gaussian heat theorem. -/
theorem responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2) :
    HasPolynomiallyBoundedC2Derivatives
      (responseFrameEnergyObservable hU hvol ν σ hν hσ P) := by
  let Φ := responseFrameEnergyObservable hU hvol ν σ hν hσ P
  let b := Φ 0
  let a := max 1 (1 / ν)
  let m := max 1 (max (2 / ν) (10 / ν ^ 2))
  have hbSq := responseFrameEnergyBaseMinimizer_norm_sq hU hvol ν σ hν hσ 0 P
  have hb : 0 ≤ b := by
    change 0 ≤ responseFrameEnergyObservable hU hvol ν σ hν hσ P 0
    rw [← hbSq]
    positivity
  have ha1 : 1 ≤ a := le_max_left _ _
  have hainv : 1 / ν ≤ a := le_max_right _ _
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmgrad : 2 / ν ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmhess : 10 / ν ^ 2 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hFactor (x : ResponseCoefficient U) :
      1 + ‖x‖ / ν ≤ a * (1 + ‖x‖) := by
    have hnorm : (1 / ν) * ‖x‖ ≤ a * ‖x‖ :=
      mul_le_mul_of_nonneg_right hainv (norm_nonneg x)
    calc
      1 + ‖x‖ / ν = 1 + (1 / ν) * ‖x‖ := by ring
      _ ≤ a + a * ‖x‖ := add_le_add ha1 hnorm
      _ = a * (1 + ‖x‖) := by ring
  have hEnergyNonneg (x : ResponseCoefficient U) : 0 ≤ Φ x := by
    have hSq := responseFrameEnergyBaseMinimizer_norm_sq hU hvol ν σ hν hσ x P
    change 0 ≤ responseFrameEnergyObservable hU hvol ν σ hν hσ P x
    rw [← hSq]
    exact sq_nonneg _
  have hValueBase (x : ResponseCoefficient U) :
      |Φ x| ≤ b * a ^ 2 * (1 + ‖x‖) ^ 2 := by
    have hVal := responseFrameEnergyObservable_value_le hU hvol ν σ hν hσ P x
    have hFactorSq : (1 + ‖x‖ / ν) ^ 2 ≤ (a * (1 + ‖x‖)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 (hFactor x)
    calc
      |Φ x| = Φ x := abs_of_nonneg (hEnergyNonneg x)
      _ ≤ (1 + ‖x‖ / ν) ^ 2 * b := by simpa [Φ, b] using hVal
      _ ≤ (a * (1 + ‖x‖)) ^ 2 * b :=
        mul_le_mul_of_nonneg_right hFactorSq hb
      _ = b * a ^ 2 * (1 + ‖x‖) ^ 2 := by ring
  have hValue (x : ResponseCoefficient U) :
      |Φ x| ≤ (b * a ^ 2 * m) * (1 + ‖x‖) ^ 2 := by
    have hc : b * a ^ 2 ≤ (b * a ^ 2) * m :=
      le_mul_of_one_le_right (by positivity) hm1
    calc
      |Φ x| ≤ b * a ^ 2 * (1 + ‖x‖) ^ 2 := hValueBase x
      _ = (b * a ^ 2) * (1 + ‖x‖) ^ 2 := by ring
      _ ≤ ((b * a ^ 2) * m) * (1 + ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = (b * a ^ 2 * m) * (1 + ‖x‖) ^ 2 := by ring
  have hGradient (x : ResponseCoefficient U) :
      ‖fderiv ℝ Φ x‖ ≤ (b * a ^ 2 * m) * (1 + ‖x‖) ^ 2 := by
    have hGrad := responseFrameEnergyObservable_fderiv_norm_le
      hU hvol ν σ hν hσ P x
    have hEnergy : Φ x ≤ b * a ^ 2 * (1 + ‖x‖) ^ 2 := by
      exact (le_abs_self _).trans (hValueBase x)
    have hcoef : (2 / ν) * (b * a ^ 2) ≤ (b * a ^ 2) * m := by
      calc
        (2 / ν) * (b * a ^ 2) ≤ m * (b * a ^ 2) :=
          mul_le_mul_of_nonneg_right hmgrad (by positivity)
        _ = (b * a ^ 2) * m := by ring
    calc
      ‖fderiv ℝ Φ x‖ ≤ (2 / ν) * Φ x := by simpa [Φ] using hGrad
      _ ≤ (2 / ν) * (b * a ^ 2 * (1 + ‖x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hEnergy (by positivity)
      _ = ((2 / ν) * (b * a ^ 2)) * (1 + ‖x‖) ^ 2 := by ring
      _ ≤ ((b * a ^ 2) * m) * (1 + ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = (b * a ^ 2 * m) * (1 + ‖x‖) ^ 2 := by ring
  refine ⟨responseFrameEnergyObservable_contDiff hU hvol ν σ hν hσ P,
    ⟨b * a ^ 2 * m, by positivity, 2, hValue, hGradient, ?_⟩⟩
  intro x H K
  have hHess := responseFrameEnergyObservable_second_fderiv_norm_le
    hU hvol ν σ hν hσ P x H K
  have hEnergy : Φ x ≤ b * a ^ 2 * (1 + ‖x‖) ^ 2 :=
    (le_abs_self _).trans (hValueBase x)
  have hcoef : (10 / ν ^ 2) * (b * a ^ 2) ≤ (b * a ^ 2) * m := by
    calc
      (10 / ν ^ 2) * (b * a ^ 2) ≤ m * (b * a ^ 2) :=
        mul_le_mul_of_nonneg_right hmhess (by positivity)
      _ = (b * a ^ 2) * m := by ring
  calc
    |fderiv ℝ (fun z => fderiv ℝ Φ z K) x H| ≤
        (10 / ν ^ 2) * Φ x * ‖H‖ * ‖K‖ := by simpa [Φ] using hHess
    _ ≤ ((10 / ν ^ 2) * (b * a ^ 2)) *
          (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ := by
      have hcoeff_nonneg : 0 ≤ 10 / ν ^ 2 := by positivity
      have hnH : 0 ≤ ‖H‖ := norm_nonneg H
      have hnK : 0 ≤ ‖K‖ := norm_nonneg K
      calc
        (10 / ν ^ 2) * Φ x * ‖H‖ * ‖K‖ ≤
            (10 / ν ^ 2) * (b * a ^ 2 * (1 + ‖x‖) ^ 2) * ‖H‖ * ‖K‖ := by
              gcongr
        _ = ((10 / ν ^ 2) * (b * a ^ 2)) *
              (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ := by ring
    _ ≤ ((b * a ^ 2) * m) * (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ := by
      have hR : 0 ≤ (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ := by positivity
      calc
        ((10 / ν ^ 2) * (b * a ^ 2)) * (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ =
            ((10 / ν ^ 2) * (b * a ^ 2)) *
              ((1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖) := by ring
        _ ≤ ((b * a ^ 2) * m) * ((1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖) :=
          mul_le_mul_of_nonneg_right hcoef hR
        _ = ((b * a ^ 2) * m) * (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ := by ring
    _ = (b * a ^ 2 * m) * (1 + ‖x‖) ^ 2 * ‖H‖ * ‖K‖ := by ring

end

end ASDExplicitGamma.Response
