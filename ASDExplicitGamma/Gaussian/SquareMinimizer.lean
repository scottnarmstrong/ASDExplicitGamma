module

public import ASDExplicitGamma.Variational.LemmaVResponse
public import Homogenization.Geometry.CubeMeasure

/-! The actual affine minimizer pair on every translated triadic square. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

local instance squareMinimizerFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Every translated triadic observation square has positive physical volume. -/
theorem square_volume_pos (Q : TriadicCube 2) :
    0 < (volume (openCubeSet Q)).toReal := by
  rw [volume_openCubeSet_toReal]
  exact cubeVolume_pos Q

/-- Correlated harmonic witnesses for the actual affine minimizer on an
arbitrary translated triadic square, retaining both physical load energies. -/
theorem square_minimizer_pair (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : BlockVec 2) :
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let M := (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
      hEll (square_volume_pos Q)
    ∃ r : H10Function U, ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (adjointCoeffField a) U,
        (hilbertBlockL2ToBlockL2 (M.toMuHilbertRealization.minimizerMap P) =ᵐ[volumeMeasureOn U]
          fun x => (blockResponsePairHalfState a u v).eval x) ∧
        ((lemmaVAffinePotential hU P.1 r).grad =ᵐ[volumeMeasureOn U]
          (blockResponsePairHalfState a u v).potential) ∧
        (2 * M.toMuHilbertRealization.muCandidate P - 2 * vecDot P.1 P.2 =
          volumeAverage U (scalarVariationEnergyIntegrand (adjointCoeffField a) v)) ∧
        (2 * M.toMuHilbertRealization.muCandidate P + 2 * vecDot P.1 P.2 =
          volumeAverage U (scalarVariationEnergyIntegrand a u)) := by
  intro U hU M
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let S := R.recoveredField M P
  have hadm := R.recoveredField_admissible M P
  obtain ⟨r, hr⟩ := hadm.isPotentialZeroTrace
  obtain ⟨u, v, hpair⟩ :=
    R.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      M hU hEll (square_volume_pos Q).ne' P
  have hgrad : (lemmaVAffinePotential hU P.1 r).grad = S.potential := by
    funext x
    simp only [lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad, hr]
    change P.1 + (S.potential x - P.1) = S.potential x
    abel
  have hE : blockEnergyAverage U a S = M.toMuHilbertRealization.muCandidate P := by
    have h := R.blockEnergyAverage_affineField_correctionPart_eq_muCandidate M P
    rw [R.affineField_correctionPart] at h
    exact h
  have hpairE : blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      M.toMuHilbertRealization.muCandidate P := by
    rw [← hE]
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hpair] with x hx
    exact congrArg (fun z => (1 / 2 : ℝ) * blockVecDot z
      (blockMatVecMul (blockCoeffField a x) z)) hx
  have hpairing : volumeAverage U (fun x => vecDot
      ((blockResponsePairHalfState a u v).potential x)
      ((blockResponsePairHalfState a u v).flux x)) = vecDot P.1 P.2 := by
    rw [← R.recoveredField_average_pairing_of_integral_eq_zero M
      (fun P' => IsPotentialZeroTraceOn.integral_eq_zero
        (R.recoveredCorrectionField M P').isPotentialZeroTrace)
      (fun P' => IsSolenoidalZeroNormalTraceOn.integral_eq_zero
        hU.isSobolevRegularDomain
        (R.recoveredCorrectionField M P').isSolenoidalZeroNormalTrace)
      (square_volume_pos Q).ne' P]
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hpair] with x hx
    exact congrArg (fun z : BlockVec 2 => vecDot z.1 z.2) hx
  have hsum :=
    blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
      a (measurableSet_openCubeSet _) hEll u v
  have hdiff :=
    volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
      a hEll u v
  refine ⟨r, u, v, ?_, ?_, ?_, ?_⟩
  · exact (lemmaV_recovered_minimizer_ae hU hEll
      (square_volume_pos Q) P).trans hpair.symm
  · rw [hgrad]
    exact hpair.symm.mono fun x hx => congrArg Prod.fst hx
  · linarith only [hpairE, hpairing, hsum, hdiff]
  · linarith only [hpairE, hpairing, hsum, hdiff]

end
end ASDExplicitGamma.Gaussian
