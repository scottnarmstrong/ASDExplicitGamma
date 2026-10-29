module

public import ASDExplicitGamma.Variational.LemmaVEnvelope
public import ASDExplicitGamma.Variational.LemmaVDefect
public import ASDExplicitGamma.Variational.LemmaVSobolev

/-! Correlated representatives of the physical Hilbert minimizer for Lemma V. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

/-- Canonical recovery of the potential/solenoidal correction space on an
open bounded convex domain. -/
def lemmaVRecoveryData {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : PotentialSolenoidalL2RecoveryData U :=
  potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
    (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain hU)

/-- The recovered minimizer is the physical representative of the canonical
Hilbert minimizer, almost everywhere. -/
theorem lemmaV_recovered_minimizer_ae {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField 2} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) (P : BlockVec 2) :
    let M := (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
      hEll hvol
    hilbertBlockL2ToBlockL2 (M.toMuHilbertRealization.minimizerMap P) =ᵐ[volumeMeasureOn U]
      (fun x => ((lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData.recoveredField M P).eval x) := by
  intro M
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let S := R.recoveredField M P
  have hS : MemBlockL2 U S.eval := R.recoveredField_memBlockL2 M P
  have hmin : toHilbertBlockL2OfBlockField hS = M.toMuHilbertRealization.minimizerMap P :=
    R.recoveredField_minimizer_eq M P
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField hS,
    coeFn_hilbertBlockL2ToBlockL2 (M.toMuHilbertRealization.minimizerMap P)] with x hx hy
  rw [hmin] at hx
  rw [hy, hx]
  simp [hilbertifyBlockField]
  rfl

/-- The canonical Hilbert minimum equals the manuscript variational minimum
on an open bounded convex domain. -/
theorem lemmaV_canonical_muCandidate_eq_Mu {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField 2} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) (P : BlockVec 2) :
    let M := (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
      hEll hvol
    M.toMuHilbertRealization.muCandidate P = Mu U P a := by
  intro M
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let S := R.recoveredField M P
  have hE : blockEnergyAverage U a S = M.toMuHilbertRealization.muCandidate P := by
    have h := R.blockEnergyAverage_affineField_correctionPart_eq_muCandidate M P
    rw [R.affineField_correctionPart] at h
    exact h
  have hle (X : BlockState 2) (hX : IsBlockMuAdmissible U P X) :
      M.toMuHilbertRealization.muCandidate P ≤ blockEnergyAverage U a X := by
    let Y := hX.toCorrectionFieldDataOfAdmissible
    have hcorr : Y.toHilbertBlockL2 ∈ M.toMuHilbertRealization.correctionSpace.correctionSpace :=
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData.mem_correctionSpace
        Y.potential_memL2 Y.flux_memL2 Y.isPotentialZeroTrace Y.isSolenoidalZeroNormalTrace
    have hconst : toHilbertBlockL2OfBlockField hX.memBlockL2_eval =
        blockVecToHilbertBlockL2Const P + Y.toHilbertBlockL2 :=
      hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    have hmem : toHilbertBlockL2OfBlockField hX.memBlockL2_eval -
        M.toMuHilbertRealization.constantField P ∈
          M.toMuHilbertRealization.correctionSpace.correctionSpace := by
      rw [hconst]
      change blockVecToHilbertBlockL2Const P + Y.toHilbertBlockL2 -
        blockVecToHilbertBlockL2Const P ∈ _
      simpa only [add_sub_cancel_left] using hcorr
    have h := M.toMuHilbertRealization.muCandidate_le_quadraticEnergy P
      (toHilbertBlockL2OfBlockField hX.memBlockL2_eval) hmem
    exact h.trans_eq (M.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
      hX.memBlockL2_eval)
  have hbdd : BddBelow (muValueSet U P a) := by
    refine ⟨M.toMuHilbertRealization.muCandidate P, ?_⟩
    rintro e ⟨X, hX, rfl⟩
    exact hle X hX
  apply le_antisymm
  · exact le_Mu_of_forall_isBlockMuAdmissible hle
  · rw [← hE]
    exact csInf_le hbdd (muValueSet_mem (R.recoveredField_admissible M P))

/-- An affine potential with its actual zero-trace correction. -/
def lemmaVAffinePotential {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (p : Vec 2) (r : H10Function U) : H1Function U :=
  H1Function.affineOnIsSobolevRegularDomain hU.isSobolevRegularDomain p + r.toH1Function

/-- Correlated primal/adjoint harmonic witnesses for the canonical minimizer.
The affine potential is supplied with an actual H¹₀ correction, so the
abstract interpolant residual hypothesis applies to it. -/
theorem lemmaV_minimizer_pair (m : ℤ) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube 2 m)) a)
    (P : BlockVec 2) :
    let U := openCubeSet (originCube 2 m)
    let hU := isOpenBoundedConvexDomain_openCubeSet (originCube 2 m)
    let M := (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
      hEll (volume_openCubeSet_originCube_toReal_pos (d := 2) m)
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
      M hU hEll (volume_openCubeSet_originCube_toReal_pos (d := 2) m).ne' P
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
    rw [← R.recoveredField_average_pairing_openCubeSet_originCube M P]
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
      (volume_openCubeSet_originCube_toReal_pos (d := 2) m) P).trans hpair.symm
  · rw [hgrad]
    exact hpair.symm.mono fun x hx => congrArg Prod.fst hx
  · linarith only [hpairE, hpairing, hsum, hdiff]
  · linarith only [hpairE, hpairing, hsum, hdiff]

end

end ASDExplicitGamma.Variational
