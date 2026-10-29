module

public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Gaussian.CovarianceTrace
public import ASDExplicitGamma.Inverse.PureFluxCovarianceRows

/-! Covariance-Hessian expansion for the actual four affine
response loads. -/

@[expose] public section

open Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped BigOperators

namespace ASDExplicitGamma.Inverse

/-- The diagonal Hessian term written using the actual response minimizer, its
localized shear, and the projected response source. -/
noncomputable def pureFluxResponseHessianDiagonal
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) : ℝ :=
  let D : EnergyHilbertData (H := HilbertBlockL2 U) :=
    responseFrameEnergyData hU hvol ν σ hν hσ k
  let V : ClosedSubmodule ℝ (EnergyCarrier D) :=
    responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let Z : EnergyCarrier D :=
    V.toSubmodule.orthogonalProjectionOnto
      (C H S + responseAdjointMap (C H) S)
  2 * inner ℝ (C H S) (C H S) - 2 * inner ℝ Z Z

/-- The complementary part of the pure-second shear source `C_H S`. -/
noncomputable def pureFluxResponseGeneratorY
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V : ClosedSubmodule ℝ (EnergyCarrier D) :=
    responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  C H S - V.toSubmodule.orthogonalProjectionOnto (C H S)

/-- The projected adjoint source `P C_H^* S` in the exact Hessian identity. -/
noncomputable def pureFluxResponseGeneratorZ
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V : ClosedSubmodule ℝ (EnergyCarrier D) :=
    responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  V.toSubmodule.orthogonalProjectionOnto (responseAdjointMap (C H) S)

private theorem pureFlux_hilbert_generator_projection_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : ClosedSubmodule ℝ E) (C : E →L[ℝ] E) (S : E)
    (hNil : C ∘L C = 0) :
    inner ℝ (C S) (C S) -
        inner ℝ
          ((V.toSubmodule.orthogonalProjectionOnto
            (C S + responseAdjointMap C S) : V.toSubmodule) : E)
          ((V.toSubmodule.orthogonalProjectionOnto
            (C S + responseAdjointMap C S) : V.toSubmodule) : E) =
      ‖C S - (V.toSubmodule.orthogonalProjectionOnto (C S) : V.toSubmodule)‖ ^ 2 +
        2 * inner ℝ S
          (C (C S - (V.toSubmodule.orthogonalProjectionOnto (C S) : V.toSubmodule))) -
      ‖((V.toSubmodule.orthogonalProjectionOnto (responseAdjointMap C S) :
          V.toSubmodule) : E)‖ ^ 2 := by
  let A := C S
  let B := responseAdjointMap C S
  let pSub : V.toSubmodule := V.toSubmodule.orthogonalProjectionOnto A
  let zSub : V.toSubmodule := V.toSubmodule.orthogonalProjectionOnto B
  let p : E := pSub
  let z : E := zSub
  let y : E := A - p
  have hA : A = y + p := by
    dsimp [y]
    abel
  have hpA (w : V.toSubmodule) : inner ℝ p (w : E) = inner ℝ A (w : E) := by
    change inner ℝ (pSub : E) (w : E) = inner ℝ A (w : E)
    exact V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right w A
  have hYorth (w : V.toSubmodule) : inner ℝ y (w : E) = 0 := by
    dsimp [y]
    rw [sub_eq_add_neg, inner_add_left, inner_neg_left, hpA]
    ring
  have hYp : inner ℝ y p = 0 := by
    have h := hYorth pSub
    simpa only [p, pSub] using h
  have hNilA : C A = 0 := by
    have h := congrArg (fun T : E →L[ℝ] E => T S) hNil
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, A] using h
  have hAB : inner ℝ A B = 0 := by
    have h := ContinuousLinearMap.adjoint_inner_left C A S
    rw [hNilA] at h
    have hBA : inner ℝ B A = 0 := by
      simpa [A, B, responseAdjointMap] using h
    calc
      inner ℝ A B = inner ℝ B A := real_inner_comm _ _
      _ = 0 := hBA
  have hPB : inner ℝ p B = inner ℝ p z := by
    change inner ℝ (pSub : E) B = inner ℝ (pSub : E) (zSub : E)
    exact (V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left pSub B).symm
  have hABsplit : inner ℝ A B = inner ℝ y B + inner ℝ p z := by
    rw [hA, inner_add_left, hPB]
  have hYB : inner ℝ y B = -inner ℝ p z := by
    nlinarith only [hAB, hABsplit]
  have hAdj : inner ℝ S (C y) = inner ℝ y B := by
    calc
      inner ℝ S (C y) = inner ℝ B y := by
        exact (ContinuousLinearMap.adjoint_inner_left C y S).symm
      _ = inner ℝ y B := real_inner_comm _ _
  have hNormA : ‖A‖ ^ 2 = ‖y‖ ^ 2 + ‖p‖ ^ 2 := by
    calc
      ‖A‖ ^ 2 = ‖y + p‖ ^ 2 := by rw [hA]
      _ = ‖y‖ ^ 2 + 2 * inner ℝ y p + ‖p‖ ^ 2 := norm_add_sq_real _ _
      _ = _ := by rw [hYp]; ring
  have hProjAdd :
      (V.toSubmodule.orthogonalProjectionOnto (A + B) : E) = p + z := by
    change ((V.toSubmodule.orthogonalProjectionOnto (A + B) : V.toSubmodule) : E) = _
    simp only [map_add]
    rfl
  have hNormProj :
      ‖(V.toSubmodule.orthogonalProjectionOnto (A + B) : E)‖ ^ 2 =
        ‖p‖ ^ 2 + 2 * inner ℝ p z + ‖z‖ ^ 2 := by
    rw [hProjAdd, norm_add_sq_real]
  calc
    inner ℝ A A -
        inner ℝ ((V.toSubmodule.orthogonalProjectionOnto (A + B) : V.toSubmodule) : E)
          ((V.toSubmodule.orthogonalProjectionOnto (A + B) : V.toSubmodule) : E) =
        ‖A‖ ^ 2 - ‖(V.toSubmodule.orthogonalProjectionOnto (A + B) : E)‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    _ = ‖y‖ ^ 2 + 2 * inner ℝ S (C y) - ‖z‖ ^ 2 := by
      rw [hNormA, hNormProj, hAdj]
      nlinarith only [hYB]
    _ = _ := by simpa [A, B, p, pSub, z, zSub, y]

/-- Exact one-half Hessian identity with the projected pure source and the
projected adjoint source. It is the per-direction form of (1.1), before any
covariance estimates are applied. -/
theorem pureFluxResponseHessianDiagonal_source_identity
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    (1 / 2 : ℝ) * pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P k H =
      ‖pureFluxResponseGeneratorY hU hvol ν σ hν hσ P k H‖ ^ 2 +
        2 * inner ℝ
          (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)
          (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H
            (pureFluxResponseGeneratorY hU hvol ν σ hν hσ P k H)) -
        ‖pureFluxResponseGeneratorZ hU hvol ν σ hν hσ P k H‖ ^ 2 := by
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V : ClosedSubmodule ℝ (EnergyCarrier D) :=
    responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  have h := pureFlux_hilbert_generator_projection_identity V (C H) S
    (responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k H H)
  change (1 / 2 : ℝ) * (2 * inner ℝ (C H S) (C H S) -
      2 * inner ℝ
        ((V.toSubmodule.orthogonalProjectionOnto
          (C H S + responseAdjointMap (C H) S) : V.toSubmodule) : EnergyCarrier D)
        ((V.toSubmodule.orthogonalProjectionOnto
          (C H S + responseAdjointMap (C H) S) : V.toSubmodule) : EnergyCarrier D)) = _
  calc
    _ = inner ℝ (C H S) (C H S) - inner ℝ
        ((V.toSubmodule.orthogonalProjectionOnto
          (C H S + responseAdjointMap (C H) S) : V.toSubmodule) : EnergyCarrier D)
        ((V.toSubmodule.orthogonalProjectionOnto
          (C H S + responseAdjointMap (C H) S) : V.toSubmodule) : EnergyCarrier D) := by ring
    _ = _ := by
      change inner ℝ (C H S) (C H S) - inner ℝ
          ((V.toSubmodule.orthogonalProjectionOnto
            (C H S + responseAdjointMap (C H) S) : V.toSubmodule) : EnergyCarrier D)
          ((V.toSubmodule.orthogonalProjectionOnto
            (C H S + responseAdjointMap (C H) S) : V.toSubmodule) : EnergyCarrier D) =
        ‖C H S - ((V.toSubmodule.orthogonalProjectionOnto (C H S) :
            V.toSubmodule) : EnergyCarrier D)‖ ^ 2 +
          2 * inner ℝ S (C H (C H S - ((V.toSubmodule.orthogonalProjectionOnto (C H S) :
            V.toSubmodule) : EnergyCarrier D))) -
          ‖((V.toSubmodule.orthogonalProjectionOnto (responseAdjointMap (C H) S) :
            V.toSubmodule) : EnergyCarrier D)‖ ^ 2
      exact h

/-- The response trace is the actual sum of diagonal Hessians at
the affine minimizer. This exposes the source and projection terms to the
q3 column and forced-source estimates without adding a bound as a premise. -/
theorem responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (H : ℕ → ResponseCoefficient U) (k : ResponseCoefficient U) :
    modelCovarianceTrace (responseFrameEnergyObservable hU hvol ν σ hν hσ P) H k =
      ∑' j, pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P k (H j) := by
  unfold modelCovarianceTrace
  apply tsum_congr
  intro j
  calc
    secondDirectionalDerivative
        (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k (H j) =
        fderiv ℝ (fun z => fderiv ℝ
          (responseFrameEnergyObservable hU hvol ν σ hν hσ P) z (H j)) k (H j) := rfl
    _ = pureFluxResponseHessianDiagonal hU hvol ν σ hν hσ P k (H j) := by
      unfold pureFluxResponseHessianDiagonal
      exact responseFrameEnergyObservable_hessian hU hvol ν σ hν hσ P k (H j) (H j)

end ASDExplicitGamma.Inverse
