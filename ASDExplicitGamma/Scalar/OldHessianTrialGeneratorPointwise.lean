module

public import ASDExplicitGamma.Scalar.OldHessianTrialActualModes
public import ASDExplicitGamma.Scalar.OldHessianTrialFifthBill
public import ASDExplicitGamma.Scalar.OldHessianTrialThirdBill
public import ASDExplicitGamma.Scalar.OldHessianTrialFourthBill
public import ASDExplicitGamma.Scalar.OldHessianTrialFlatBills

/-! Pointwise (almost sure) ten-bill bound on the actual OLD Hessian sum. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The sum of the ten integrable bill envelopes and the affine energy. -/
def oldHessianEnvelopeSum (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldHessianSecondBill M m b ω+
  ((431/500:ℝ)^2*oldHessianMinusAffineEnergy M m b (q3ModelLength (m+1)) ω+
    oldHessianFirstBill M m b ω)+
  (oldHessianThirdBill M m b ω+oldHessianFifthBill M m b ω+
    oldHessianFourthBill M m b ω+oldHessianSeventhBill M m b ω)+
  oldHessianNinthBill M m b ω+
  (oldHessianSixthBill M m b ω+oldHessianTenthBill M m b ω)+
  oldHessianFlatTangentEnvelope M m b ω

/-- The actual normalized inverse trace of the OLD parent response. -/
def oldHessianInverseTrace (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 (m+129)))
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
      (oldHessianOldOpenCoefficient (m+129) m ω))).lowerRight

/-- Envelope sum, signed inverse-trace bulk and signed Dirichlet bulk of one OLD sample. -/
def oldHessianPointwiseCap (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldHessianEnvelopeSum M m b ω-
  (431/500:ℝ)*b^2*(oldHessianInverseTrace M m ω-2)-
  2*(431/500:ℝ)*(b^2-oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1))/2)

/-- Almost every OLD sample: the complete actual physical Hessian sum is
summable and below the ten-bill pointwise cap. -/
theorem old_hessian_actual_generator_pointwise
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) (hb : 0<b) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun n => oldHessianActualHessianMode M m b n ω) ∧
      (∑' n,oldHessianActualHessianMode M m b n ω)≤oldHessianPointwiseCap M m b ω := by
  have h3 := (old_hessian_actual_third_bill M h hM hg N hpast m hm b).2.1
  have h4 := (old_hessian_actual_fourth_bill M h hM hg N hpast m hm b).2.1
  have h5 := (old_hessian_actual_fifth_bill M h hM hg N hpast m hm b hb).2.1
  have h7 := (old_hessian_actual_seventh_bill M h hM hg N hpast m hm b).2.1
  have h9 := (old_hessian_actual_ninth_bill M h hM hg N hpast m hm b).2.1
  have h610 := (old_hessian_actual_sixth_tenth_bills M h hM hg N hpast m hm b).2.2.1
  have h8 := (old_hessian_actual_eighth_bill M h hM hg N hpast m hm b hb).2.1
  have h2 := (old_hessian_actual_second_bill M h hM hg N hpast m hm b).2.1
  have hid := old_hessian_actual_full_affine_identity M h hM hg N hpast m hm b
  filter_upwards [h3,h4,h5,h7,h9,h610,h8,h2,hid] with ω e3 e4 e5 e7 e9 e610 e8 e2 eid
  dsimp only at eid e8
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let σ := Annealed.sigmaBar M m
  let L := q3ModelLength (m+1)
  have hσ := (Annealed.sigmaBar_characterization M m).1
  have hjr := old_hessian_actual_joint_residual_energy (m+129) 133 M.nu σ M.nu_pos hσ k b L
  dsimp only at hjr
  have hrr : HasSum (fun n => oldHessianResidualModeEnergy M m b n ω)
      (∑ i : Fin 2,∑' j,oldSignedEnergyPairing Q M.nu σ k
        (oldHessianMixedBottomResidual Q 133 134 M.nu σ M.nu_pos hσ k b L j i)
        (oldHessianMixedBottomResidual Q 133 134 M.nu σ M.nu_pos hσ k b L j i)) :=
    hasSum_sum (fun i _ => (hjr.1 i).hasSum)
  have hzs := old_hessian_actual_minus_flat_envelope M m b L ω
  have hdir := (old_signed_flat_minus_complete_energy Q b L).1
  have hsoN : HasSum (fun n => ∑ i : Fin 2,oldHessianSourceOscillationTerm M m b (n,i) ω)
      (∑' p,oldHessianSourceOscillationTerm M m b p ω) :=
    e7.1.hasSum.prod_fiberwise (fun n => (hasSum_fintype _))
  have hT := ((((hrr.add (hzs.1.hasSum.mul_left ((431/500:ℝ)^2))).add
    (eid.sub (hsoN.mul_left (2*(431/500:ℝ))))).add e9.1.hasSum).add
    ((e8.1.hasSum.sub (hdir.hasSum.mul_left (2*(431/500:ℝ)))).sub e610.1.hasSum))
  have hHs : Summable (fun n => oldHessianActualHessianMode M m b n ω) := by
    unfold oldHessianActualHessianMode
    exact summable_sum (fun i _ => old_signed_physical_hessian_summable (m+129) M.nu σ M.nu_pos hσ k
      (0,basisVec i) b L)
  have hle := hasSum_le (fun n => old_hessian_actual_mode_decomposition M m b n ω) hHs.hasSum hT
  refine ⟨hHs,hle.trans ?_⟩
  have h1 := (old_hessian_actual_first_bill M h hM hg N hpast m hm b).2.1 ω
  have hY : oldSignedFlatBoundaryEnergy Q b L=2*(b^2-∑' n,oldSignedFlatDirichletModeEnergy Q b L n) := by
    unfold oldSignedFlatBoundaryEnergy
    exact (old_signed_flat_boundary_energy_trace Q b L).tsum_eq
  have a3 := neg_abs_le (((431/500:ℝ)*b^2)*oldHessianPrincipalSpatialCross Q 133 M.nu σ M.nu_pos hσ k)
  have a5 := neg_abs_le ((2*(431/500:ℝ))*oldHessianCovarianceSpatialCross Q 133 M.nu σ M.nu_pos hσ k b L)
  have a4 := le_abs_self ((2*(431/500:ℝ))*(∑' p,oldHessianCenteredAffineTerm M m b p ω))
  have a7 := neg_abs_le ((2*(431/500:ℝ))*(∑' p,oldHessianSourceOscillationTerm M m b p ω))
  have a9 := le_abs_self (∑' n,oldHessianMixedFeedbackTerm M m b n ω)
  have a610 := neg_abs_le (∑' n,oldHessianMinusFeedbackTerm M m b n ω)
  have b3 := e3
  have b5 := e5
  have b4 := e4.2
  have b7 := e7.2
  have b9 := e9.2
  have b610 := e610.2
  have b8 := e8.2
  have b2 : (∑ i : Fin 2,∑' j,oldSignedEnergyPairing Q M.nu σ k
        (oldHessianMixedBottomResidual Q 133 134 M.nu σ M.nu_pos hσ k b L j i)
        (oldHessianMixedBottomResidual Q 133 134 M.nu σ M.nu_pos hσ k b L j i))≤
      oldHessianSecondBill M m b ω := e2
  unfold oldHessianPointwiseCap oldHessianEnvelopeSum oldHessianInverseTrace
  rw [hY]
  linarith only [a3,a5,a4,a7,a9,a610,b3,b5,b4,b7,b9,b610,b8,b2,h1]

end
end ASDExplicitGamma.Scalar
