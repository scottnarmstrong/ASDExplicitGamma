module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredAffineSpatial
public import ASDExplicitGamma.Scalar.OldHessianTrialActualAffineReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredEnvelope

/-! Actual complete centered source/affine receiver pairing in the OLD law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Exact substitution of the actual OLD medium and original fine source
into the complete centered spatial energy. -/
theorem old_hessian_centered_spatial_physical_energy (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    oldHessianCenteredSpatialEnergy (originCube 2 (m+129)) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
      b (q3ModelLength (m+1))=oldHessianCenteredSourceEnergy M m b ω := rfl

/-- One literal actual centered-source/original-minus-affine cross. -/
def oldHessianCenteredAffineTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (p : whiteBasisIndex×Fin 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldHessianCenteredAffineSpatialTerm (originCube 2 (m+129)) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
    b (q3ModelLength (m+1)) p

/-- The full signed physical centered affine cross converges and pays the
same two correlated envelopes used in the exact fourth scalar error bill.
All receiver convergence and source energy inputs are proved internally. -/
theorem old_hessian_actual_centered_affine_pairing
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun p => oldHessianCenteredAffineTerm M m b p ω) ∧
        |∑' p,oldHessianCenteredAffineTerm M m b p ω|≤
          Real.sqrt (oldHessianCenteredSourceEnvelope M m b ω)*
            Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω) := by
  filter_upwards [old_hessian_actual_centered_source_envelope M h hM hg N hpast m hm b,
    old_hessian_actual_minus_affine_receiver_energy M h hM hg N hpast m hm b (q3ModelLength (m+1))]
    with ω hsource hreceiver
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let L := q3ModelLength (m+1)
  have hR : Summable (oldHessianMinusAffineSpatialEnergy Q 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L) := hreceiver.1
  have hh := old_hessian_centered_affine_spatial_pairing Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L hR
  have hS : oldHessianCenteredSpatialEnergy Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L≤oldHessianCenteredSourceEnvelope M m b ω := by
    rw [old_hessian_centered_spatial_physical_energy]
    exact hsource
  have hRcap : (∑' p,oldHessianMinusAffineSpatialEnergy Q 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L p)≤
      oldHessianMinusAffineReceiverEnvelope M m b L ω := hreceiver.2
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hRcap)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

end
end ASDExplicitGamma.Scalar
