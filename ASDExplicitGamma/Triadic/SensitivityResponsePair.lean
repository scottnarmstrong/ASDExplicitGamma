module

public import ASDExplicitGamma.Variational.LemmaVResponse
public import Homogenization.Geometry.CubeMeasure

/-! The correlated Lemma V load pair on an arbitrary triadic square. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational

instance sensitivitySquareFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  exact (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

noncomputable section

private theorem sensitivity_halfPair_potential {U : Set (Vec 2)}
    (a : CoeffField 2)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (adjointCoeffField a) U)
    (x : Vec 2) :
    (blockResponsePairHalfState a u v).potential x =
      (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := by
  change (((1 / 2 : ℝ) • blockResponsePairState a u v).eval x).1 = _
  rw [BlockState.eval_smul]
  rfl

/-- The correlated primal/adjoint load representation on any open triadic
square.  This generic version avoids an origin-only averaging hypothesis. -/
theorem sensitivity_response_load_pair (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let hv : 0 < (volume U).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos Q
    let a := responseFramePlanarCoefficientField ν σ k
    let E := responseFrameEnergyObservable hU.isOpen.measurableSet hv ν σ hν hσ P
    ∃ r : H10Function U, ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (adjointCoeffField a) U,
        ((lemmaVAffinePotential hU P.1 r).grad =ᵐ[volumeMeasureOn U]
          fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2) ∧
        (E k - 2 * vecDot P.1 P.2 =
          volumeAverage U (scalarVariationEnergyIntegrand (adjointCoeffField a) v)) ∧
        (E k + 2 * vecDot P.1 P.2 =
          volumeAverage U (scalarVariationEnergyIntegrand a u)) ∧
        IsResponseMaximizer U (-P.1) P.2 a u ∧
        IsResponseMaximizer U (-P.1) (-P.2) (adjointCoeffField a) v ∧
        (∀ H : ResponseCoefficient U,
          (fderiv ℝ E k H = 2 * volumeAverage U (fun x =>
            (responseCoefficientExtension H x / σ) * vecDot (v.toH1.grad x)
              (matVecMul responsePlanarJ
                ((lemmaVAffinePotential hU P.1 r).grad x)))) ∧
          (fderiv ℝ E k H = 2 * volumeAverage U (fun x =>
            -(responseCoefficientExtension H x / σ) * vecDot (u.toH1.grad x)
              (matVecMul responsePlanarJ
                ((lemmaVAffinePotential hU P.1 r).grad x))))) := by
  intro U hU hv a E
  have hEll := responseFramePlanarCoefficientField_isElliptic
    hU.isOpen.measurableSet ν σ hν hσ k
  let M := (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
    hEll hv
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let S := R.recoveredField M P
  have hadm := R.recoveredField_admissible M P
  obtain ⟨r, hr⟩ := hadm.isPotentialZeroTrace
  obtain ⟨u, v, hpair⟩ :=
    R.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      M hU hEll hv.ne' P
  have hrep := lemmaV_recovered_minimizer_ae hU hEll hv P
  have hgrad : (lemmaVAffinePotential hU P.1 r).grad = S.potential := by
    funext x
    simp only [lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad, hr]
    change P.1 + (S.potential x - P.1) = S.potential x
    abel
  let V := lemmaVAffinePotential hU P.1 r
  have hmid : V.grad =ᵐ[volumeMeasureOn U]
      fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2 := by
    filter_upwards [hpair] with x hx
    have hstate : S.eval x = (blockResponsePairHalfState a u v).eval x := hx.symm
    have hp : S.potential x = (blockResponsePairHalfState a u v).potential x :=
      congrArg Prod.fst hstate
    rw [hgrad, hp, sensitivity_halfPair_potential]
    ext i
    change (1 / 2 : ℝ) * (u.toH1.grad x i + v.toH1.grad x i) = _
    ring
  have hstateEnergy : blockEnergyAverage U a S = M.toMuHilbertRealization.muCandidate P := by
    have hh := R.blockEnergyAverage_affineField_correctionPart_eq_muCandidate M P
    rw [R.affineField_correctionPart] at hh
    exact hh
  have hpairE : blockEnergyAverage U a
      (blockResponsePairHalfState a u v) = M.toMuHilbertRealization.muCandidate P := by
    rw [← hstateEnergy]
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hpair] with x hx
    exact congrArg (fun z => (1 / 2 : ℝ) * blockVecDot z
      (blockMatVecMul (blockCoeffField a x) z)) hx
  have hpairing : volumeAverage U (fun x =>
      vecDot ((blockResponsePairHalfState a u v).potential x)
        ((blockResponsePairHalfState a u v).flux x)) = vecDot P.1 P.2 := by
    rw [← R.recoveredField_average_pairing_of_integral_eq_zero M
      (fun P' => IsPotentialZeroTraceOn.integral_eq_zero
        (R.recoveredCorrectionField M P').isPotentialZeroTrace)
      (fun P' => IsSolenoidalZeroNormalTraceOn.integral_eq_zero
        hU.isSobolevRegularDomain
        (R.recoveredCorrectionField M P').isSolenoidalZeroNormalTrace)
      hv.ne' P]
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hpair] with x hx
    exact congrArg (fun z : BlockVec 2 => vecDot z.1 z.2) hx
  let uAdjAdj : AHarmonicFunction (adjointCoeffField (adjointCoeffField a)) U := by
    refine ⟨u.toH1, ?_⟩
    rw [adjointCoeffField_adjointCoeffField]
    exact u.isHarmonic
  have hpairFlip : (fun x =>
      (blockResponsePairHalfState (adjointCoeffField a) v uAdjAdj).eval x) =ᵐ[volumeMeasureOn U]
      fun x => (S.flipFlux).eval x := by
    filter_upwards [hpair] with x hx
    have hflipPair :
        (blockResponsePairHalfState (adjointCoeffField a) v uAdjAdj).eval x =
          blockVecFlipFlux ((blockResponsePairHalfState a u v).eval x) := by
      have htr : matTranspose (matTranspose (a x)) = a x := by
        ext i j
        rfl
      change (1 / 2 : ℝ) • (blockResponsePairState (adjointCoeffField a) v uAdjAdj).eval x =
        blockVecFlipFlux ((1 / 2 : ℝ) • (blockResponsePairState a u v).eval x)
      apply Prod.ext
      · funext i
        change ((1 / 2 : ℝ) • (v.toH1.grad x + uAdjAdj.toH1.grad x)) i =
          ((1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x)) i
        simp only [uAdjAdj, Pi.smul_apply, Pi.add_apply]
        rw [add_comm]
      · funext i
        change ((1 / 2 : ℝ) •
            (matVecMul (matTranspose (a x)) (v.toH1.grad x) -
              matVecMul (matTranspose (matTranspose (a x))) (uAdjAdj.toH1.grad x))) i =
          (-((1 / 2 : ℝ) •
            (matVecMul (a x) (u.toH1.grad x) -
              matVecMul (matTranspose (a x)) (v.toH1.grad x)))) i
        simp only [uAdjAdj, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
        rw [htr]
        ring
    have hresult : (blockResponsePairHalfState (adjointCoeffField a) v uAdjAdj).eval x =
        (S.flipFlux).eval x := by
      calc
        (blockResponsePairHalfState (adjointCoeffField a) v uAdjAdj).eval x =
            blockVecFlipFlux ((blockResponsePairHalfState a u v).eval x) := hflipPair
        _ = blockVecFlipFlux (S.eval x) := congrArg blockVecFlipFlux hx
        _ = (S.flipFlux).eval x := by
          change (S.potential x, -S.flux x) = (S.potential x, -S.flux x)
          rfl
    simpa [uAdjAdj] using hresult
  have hadmFlip : IsBlockMuAdmissible U (blockVecFlipFlux P) S.flipFlux :=
    isBlockMuAdmissible_flipFlux hadm
  have hfirstU := scalarFirstVariation_neg_left_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
    a hU.isOpen.measurableSet hEll P.1 P.2 u v S hpair hadm
  have hmaxU := isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
    U a hEll (-P.1) P.2 u hfirstU
  have hEllAdj := isEllipticFieldOn_adjointCoeffField hEll
  have hfirstV := scalarFirstVariation_neg_left_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
    (adjointCoeffField a) hU.isOpen.measurableSet hEllAdj P.1 (-P.2) v uAdjAdj S.flipFlux
    hpairFlip hadmFlip
  have hmaxV := isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
    U (adjointCoeffField a) hEllAdj (-P.1) (-P.2) v hfirstV
  have hsum := blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
    a hU.isOpen.measurableSet hEll u v
  have hdiff := volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
    a hEll u v
  have hE : E k = 2 * M.toMuHilbertRealization.muCandidate P := by
    change responseFrameEnergyObservable hU.isOpen.measurableSet hv ν σ hν hσ P k = _
    rw [lemmaV_observable_eq_twice_muCandidate hU.isOpen.measurableSet hv ν σ hν hσ P k]
    rw [← lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hv ν σ hν hσ k]
  refine ⟨r, u, v, hmid, ?_, ?_, hmaxU, hmaxV, ?_⟩
  · rw [hE]
    exact (by linarith only [hpairE, hpairing, hsum, hdiff])
  · rw [hE]
    exact (by linarith only [hpairE, hpairing, hsum, hdiff])
  · intro H
    have hlower := blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
      a hEll u v
    have hcore : fderiv ℝ E k H = 2 * volumeAverage U (fun x =>
        -(responseCoefficientExtension H x / σ) *
          vecDot ((1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x))
            (matVecMul responsePlanarJ
              ((lemmaVAffinePotential hU P.1 r).grad x))) := by
      rw [lemmaV_load_first_variation]
      rw [← lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hv ν σ hν hσ k]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hpair, hrep, hlower] with x hx hr hl
      have hstate : S.eval x = (blockResponsePairHalfState a u v).eval x := hx.symm
      have hminstate :
          (hilbertBlockL2ToBlockL2 (M.toMuHilbertRealization.minimizerMap P) x) = S.eval x := by
        simpa [S] using hr
      have hfirst : (hilbertBlockL2ToBlockL2
          (M.toMuHilbertRealization.minimizerMap P) x).1 =
            (lemmaVAffinePotential hU P.1 r).grad x := by
        exact (congrArg Prod.fst hminstate).trans (congrFun hgrad x).symm
      have hconj : lemmaVConjugateGradient ν σ
          (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2
            (M.toMuHilbertRealization.minimizerMap P) x) =
            (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x) := by
        rw [← lemmaV_planar_lower_image ν σ _ hν hσ, hminstate.trans hstate]
        exact hl
      rw [hconj, hfirst]
    constructor
    · rw [hcore]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hmid] with x hx
      have hvec : (lemmaVAffinePotential hU P.1 r).grad x =
          (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := by
        funext i
        rw [congrFun hx i]
        simp [div_eq_mul_inv, mul_comm]
      rw [hvec]
      exact lemmaV_halfPair_envelope_plus ((responseCoefficientExtension H x) / σ)
        (u.toH1.grad x) (v.toH1.grad x)
    · rw [hcore]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hmid] with x hx
      have hvec : (lemmaVAffinePotential hU P.1 r).grad x =
          (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := by
        funext i
        rw [congrFun hx i]
        simp [div_eq_mul_inv, mul_comm]
      rw [hvec]
      exact lemmaV_halfPair_envelope_minus ((responseCoefficientExtension H x) / σ)
        (u.toH1.grad x) (v.toH1.grad x)

end

end ASDExplicitGamma.Triadic

end
