module

public import ASDExplicitGamma.Response.Analytic
public import ASDExplicitGamma.Variational.LemmaVAlgebra
public import Homogenization.CoarseGraining.BlockFormalism.MatrixIdentities

/-! The physical first variation of each load, as an averaged skew pairing. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

private theorem lemmaV_representative_hilbert {U : Set (Vec 2)} (X : HilbertBlockL2 U) :
    toHilbertBlockL2OfBlockField (hilbertBlockL2ToBlockL2 X).property = X := by
  apply Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (hilbertBlockL2ToBlockL2 X).property,
    coeFn_hilbertBlockL2ToBlockL2 X] with x hx hX
  rw [hx]
  change HilbertBlockVec.ofBlockVec (hilbertBlockL2ToBlockL2 X x) = X x
  rw [hX]
  simp

/-- The bilinear energy of arbitrary Hilbert fields is their physical pairing.
The operator acts on X, matching the upstream energy convention. -/
theorem lemmaV_muSystem_bilinear_eq_volumeAverage {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField 2}
    (M : MuOperatorSystemData U a) (X Y : HilbertBlockL2 U) :
    M.toMuHilbertRealization.energyBilin X Y =
      volumeAverage U (fun x => blockVecDot (hilbertBlockL2ToBlockL2 Y x)
        (blockMatVecMul (blockCoeffField a x) (hilbertBlockL2ToBlockL2 X x))) := by
  have h := M.toMuOperatorRealization.energyBilin_eq_volumeAverage_swap_of_memBlockL2
    (hilbertBlockL2ToBlockL2 Y).property (hilbertBlockL2ToBlockL2 X).property
  rw [lemmaV_representative_hilbert, lemmaV_representative_hilbert] at h
  exact h

/-- The lower block image is exactly the conjugate gradient in the fixed frame. -/
theorem lemmaV_planar_lower_image (ν σ κ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (X : BlockVec 2) :
    (blockMatVecMul (blockMatrixOfCoeff
      (responsePlanarCoefficient (ν / σ) (κ / σ))) X).2 =
      lemmaVConjugateGradient ν σ κ X := by
  have hsym : symmPart (responsePlanarCoefficient (ν / σ) (κ / σ)) =
      (ν / σ) • (1 : Mat 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmPart, responsePlanarCoefficient, responsePlanarJ]
  have hskew : skewPart (responsePlanarCoefficient (ν / σ) (κ / σ)) =
      (κ / σ) • responsePlanarJ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [skewPart, responsePlanarCoefficient, responsePlanarJ]
    ring
  have hinv : ((ν / σ) • (1 : Mat 2))⁻¹ = (σ / ν) • (1 : Mat 2) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  rcases X with ⟨p, q⟩
  rw [blockMatVecMul_blockMatrixOfCoeff_snd, hsym, hskew, hinv]
  simp only [lemmaVConjugateGradient, smul_matVecMul, matVecMul_one]

/-- The observable is twice the canonical Hilbert minimum at its coefficient. -/
theorem lemmaV_observable_eq_twice_muCandidate {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : MeasurableSet U)
    (hvol : 0 < (volume U).toReal) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k : ResponseCoefficient U) :
    responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
      2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.muCandidate P := by
  change 2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (0 + k)).toMuHilbertRealization.muCandidate P = _
  rw [zero_add]

/-- The physical system has exactly the canonical elliptic realization. -/
theorem lemmaV_responseSystem_eq_canonical {U : Set (Vec 2)}
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) :
    (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
      (responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k) hvol =
      responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k := rfl

/-- First variation per load, on the original coefficient parameter space.
The only analytic assumptions are finite positive domain volume and positive
symmetric coefficient and frame. H is any bounded continuous direction. -/
theorem lemmaV_load_first_variation {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k H =
      2 * volumeAverage U (fun x =>
        -(responseCoefficientExtension H x / σ) *
          vecDot (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
            (hilbertBlockL2ToBlockL2
              ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x))
            (matVecMul responsePlanarJ
              (hilbertBlockL2ToBlockL2
                ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1)) := by
  rw [responseFrameEnergyObservable_fderiv]
  let M := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k
  let X := M.toMuHilbertRealization.minimizerMap P
  have hdown : (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H
      (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)).down =
      responseShearL2Operator σ hσ H X := by
    simp [responseFrameEnergyShearFamily, responseEnergyShearFamilyLinear,
      responseFrameEnergyBaseMinimizer, X, M]
    rfl
  change 2 * M.toMuHilbertRealization.energyBilin X
    ((responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H
      (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)).down) = _
  rw [hdown, lemmaV_muSystem_bilinear_eq_volumeAverage]
  congr 1
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H X] with x hx
  rw [hx]
  change blockVecDot (responseShearCorrection σ (responseCoefficientExtension H x)
    (hilbertBlockL2ToBlockL2 X x))
    (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient (ν / σ)
      (responseCoefficientExtension k x / σ))) (hilbertBlockL2ToBlockL2 X x)) = _
  rw [blockVecDot, responseShearCorrection]
  simp only [vecDot_zero_left, zero_add, vecDot_neg_left, vecDot_smul_left]
  rw [lemmaV_planar_lower_image ν σ _ hν hσ]
  rw [vecDot_comm]
  ring

/-- The same actual-response derivative in physical flux variables. The scalar
direction H represents the planar skew matrix H J; its frame normalization
is inside the shear, while the external factor is the molecular 2/ν. -/
theorem lemmaV_load_first_variation_physical {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    let X := hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap P)
    fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k H =
      -(2/ν) * volumeAverage U (fun x =>
        vecDot ((X x).2 - (responseCoefficientExtension k x / σ) •
          matVecMul responsePlanarJ (X x).1)
          (responseCoefficientExtension H x • matVecMul responsePlanarJ (X x).1)) := by
  dsimp only
  let X := hilbertBlockL2ToBlockL2
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap P)
  change fderiv ℝ (responseFrameEnergyObservable hU hvol ν σ hν hσ P) k H =
    -(2/ν) * volumeAverage U (fun x =>
      vecDot ((X x).2 - (responseCoefficientExtension k x / σ) •
        matVecMul responsePlanarJ (X x).1)
        (responseCoefficientExtension H x • matVecMul responsePlanarJ (X x).1))
  rw [lemmaV_load_first_variation]
  have hpoint : (fun x => -(responseCoefficientExtension H x / σ) *
      vecDot (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
        (X x))
        (matVecMul responsePlanarJ (X x).1)) =
      (-(1/ν : ℝ)) • (fun x => vecDot
        ((X x).2 -
          (responseCoefficientExtension k x / σ) • matVecMul responsePlanarJ
            (X x).1)
        (responseCoefficientExtension H x • matVecMul responsePlanarJ
          (X x).1)) := by
    funext x
    simp only [lemmaVConjugateGradient, vecDot_smul_left, vecDot_smul_right,
      Pi.smul_apply, smul_eq_mul]
    field_simp [hν.ne', hσ.ne']
  change 2 * volumeAverage U (fun x =>
      -(responseCoefficientExtension H x / σ) *
        vecDot (lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (X x))
          (matVecMul responsePlanarJ (X x).1)) = _
  rw [hpoint, volumeAverage_smul]
  ring

end

end ASDExplicitGamma.Variational
