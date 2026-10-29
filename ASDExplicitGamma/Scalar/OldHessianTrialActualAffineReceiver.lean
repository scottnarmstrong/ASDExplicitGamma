module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialAffineReceiverColumns

/-! The original minus-mean affine TOP receiver, with actual mode convergence. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Actual fine-cell reciprocal affine receiver for each original physical
minus-mode mean column. It is not replaced by a scalar proxy. -/
def oldHessianMinusAffineReceiverTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (p : whiteBasisIndex×Fin 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldHessianMinusAffineSpatialEnergy (originCube 2 (m+129)) 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω) b L p

/-- Complete actual affine receiver modes converge a.e. and are dominated
by the integrable original-mean envelope, with all weights and banks proved. -/
theorem old_hessian_actual_minus_affine_receiver_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun p => oldHessianMinusAffineReceiverTerm M m b L p ω) ∧
        (∑' p,oldHessianMinusAffineReceiverTerm M m b L p ω)≤
          oldHessianMinusAffineReceiverEnvelope M m b L ω := by
  let Q := originCube 2 (m+129)
  let q := oldHessianMinusMeanColumn Q 134 b L
  have hbank := old_hessian_minus_mean_bank Q 134 b L
  have hs := old_hessian_cell_directional_weighted_series M h hM hg N hpast m hm q hbank.1
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q 134),
        let k := oldHessianOldOpenCoefficient (m+129) m ω
        let kU := oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k
        let S := oldSignedFrameCanonicalField U.val M.nu (Annealed.sigmaBar M m) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 kU (q p U,0)
        let J := oldSignedDualReflection U.val M.nu (Annealed.sigmaBar M m) kU S
        vectorWeakHaarEnergy U.val (fun x => (S x).1-q p U)+vectorWeakHaarEnergy U.val (fun x => (J x).1)≤
          oldHessianCellDirectionalTheta M m U.val (q p U) ω :=
    ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun U =>
      old_hessian_actual_cell_top_directional_join M h hM hg N hpast m hm U.val U.property (q p U)))
  filter_upwards [hs.1,hall] with ω hsum hω
  have hn (p) : 0≤oldHessianMinusAffineReceiverTerm M m b L p ω :=
    old_signed_cell_average_nonneg _ _ _ (fun U => vectorWeakHaarEnergy_nonneg U.val _)
  have hb (p) : oldHessianMinusAffineReceiverTerm M m b L p ω≤
      oldSignedCellAverage Q 134 (fun U => oldHessianCellDirectionalTheta M m U.val (q p U) ω) := by
    apply old_signed_cell_average_mono
    intro U
    exact (le_add_of_nonneg_left (vectorWeakHaarEnergy_nonneg U.val _)).trans (hω p U)
  have ha := hsum.of_nonneg_of_le hn hb
  exact ⟨ha,ha.tsum_le_tsum hb hsum⟩

end
end ASDExplicitGamma.Scalar
