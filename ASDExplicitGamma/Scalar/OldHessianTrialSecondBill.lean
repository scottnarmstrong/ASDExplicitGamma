module

public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedSource

/-! The second OLD error bill is the actual projected mixed residual square. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- Complete actual mixed residual energy before taking the OLD-law mean. -/
def oldHessianResidualSpatialEnergy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  ∑ i : Fin 2,∑' j : whiteBasisIndex,
    let R := oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L j i
    oldSignedEnergyPairing Q nu sigma k R R

/-- Nonnegative integrable source-square majorant for the second bill. -/
def oldHessianSecondBill (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ := oldHessianGroupedBank M m ω*
      oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω

/-- The actual projected residual is paid by precisely the frozen S2
expression; the mixed source is kept inside the original fine projection. -/
theorem old_hessian_actual_second_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianSecondBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        oldHessianResidualSpatialEnergy (originCube 2 (m+129)) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
          b (q3ModelLength (m+1))≤oldHessianSecondBill M m b ω) ∧
      (∫ ω,oldHessianSecondBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        b^2*evalReal scalarRealEnv lowerTerm2Expr := by
  have hh := old_hessian_actual_source_square_certified M h hM hg N hpast m hm b
  refine ⟨hh.1,?_,hh.2⟩
  filter_upwards [old_hessian_actual_source_residual_envelope M h hM hg N hpast m hm] with ω hω
  exact (hω b (q3ModelLength (m+1))).2

end
end ASDExplicitGamma.Scalar
