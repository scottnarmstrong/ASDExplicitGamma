module

public import ASDExplicitGamma.Scalar.OldHessianTrialMixedCellFeedback
public import ASDExplicitGamma.Native.OldSignedFeedbackLoadPartition

/-! Complete original parent mixed feedback after genuine fine-cell assembly. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The unchanged parent's actual two-bottom-load feedback against R_mix. -/
def oldHessianMixedFeedbackMode (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (j : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (.inr i)))
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis j))
      (oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L j i))

/-- The full actual signed mixed feedback is absolutely summable and pays
exactly the spatial average of its joint local factors, before expectation. -/
theorem old_hessian_actual_mixed_global_feedback (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let a := responseFramePlanarCoefficientField nu sigma k
    Summable (oldHessianMixedFeedbackMode Q coarse nu sigma hnu hsigma k b L) ∧
    |∑' j,oldHessianMixedFeedbackMode Q coarse nu sigma hnu hsigma k b L j|≤
      oldSignedCellAverage Q (coarse+1) (fun U => oldSignedDerivativeKappa (cubeScaleFactor U.val) b L.val*
        (Real.sqrt 2+Real.sqrt (oldHessianBottomPairedCellEnergy Q U.val nu sigma hnu hsigma k))*
        (((63/50:ℝ)*oldSignedInverseHistory U.val a)*Real.sqrt (∑' p,
          vectorPositiveHaarEnergy U.val (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p)))) := by
  intro Q a
  let f := fun j (U : OldSignedCellIndex Q (coarse+1)) =>
    oldHessianMixedFeedbackCellMode Q coarse nu sigma hnu hsigma k b L j U
  have he (j) : oldHessianMixedFeedbackMode Q coarse nu sigma hnu hsigma k b L j=
      oldSignedCellAverage Q (coarse+1) (f j) :=
    old_signed_patched_feedback_load_partition Q (coarse+1) nu sigma hnu hsigma k b L j
      (fun i : Fin 2 => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (.inr i)))
      (fun i : Fin 2 => oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L j i)
      (fun _ => Lp.memLp _) (fun i => old_hessian_mixed_bottom_source_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L j i)
  have hh := old_signed_cell_average_series_bound Q (coarse+1) f _
    (fun U => (old_hessian_actual_mixed_cell_feedback n coarse nu sigma hnu hsigma k b L U).1)
    (fun U => (old_hessian_actual_mixed_cell_feedback n coarse nu sigma hnu hsigma k b L U).2)
  simpa only [←he] using hh

/-- The complete actual source energy commutes with its genuine fine
cell partition only after every positive cell series has been proved convergent. -/
theorem old_hessian_full_source_cell_average (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    oldSignedCellAverage (originCube 2 n) (coarse+1) (fun U => ∑' p,
      vectorPositiveHaarEnergy U.val (oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L p))=
    ∑ i : Fin 2,∑' j : whiteBasisIndex,
      oldHessianBrokenColumnEnergy (originCube 2 n) (coarse+1) (fun _U =>
        oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L (j,i)) := by
  have hs := old_signed_cell_average_series (originCube 2 n) (coarse+1)
    (fun p U => vectorPositiveHaarEnergy U.val
      (oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L p))
    (fun U => old_hessian_full_source_cell_series n coarse nu sigma hnu hsigma k b L U)
  exact hs.2.symm.trans (old_hessian_full_mode_series n coarse nu sigma hnu hsigma k b L).2

end
end ASDExplicitGamma.Scalar
