module

public import ASDExplicitGamma.Scalar.OldHessianTrialFullModeColumns
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusOscillationSeries

/-! Literal full mixed-source pairing with the original reciprocal minus oscillations. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual signed seventh-bill cross, mode by mode, on the original cells. -/
def oldHessianSourceOscillationTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (p : whiteBasisIndex×Fin 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let L := q3ModelLength (m+1)
  oldSignedCellAverage Q 134 (fun U => cubeAverage U.val (fun x =>
    vecDot (oldHessianMinusOscillationColumn Q 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L p U x)
      (oldHessianFullModeColumn Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k b L p x)))

/-- The complete signed physical cross converges and keeps the actual
correlated source and matrix envelopes. No spatial estimate is a premise. -/
theorem old_hessian_actual_source_oscillation_pairing
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun p => oldHessianSourceOscillationTerm M m b p ω) ∧
        |∑' p,oldHessianSourceOscillationTerm M m b p ω|≤
          Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)*
            Real.sqrt (oldHessianGroupedBank M m ω*
              oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω) := by
  filter_upwards [old_hessian_actual_source_residual_envelope M h hM hg N hpast m hm,
    old_hessian_actual_minus_oscillation_series M h hM hg N hpast m hm b (q3ModelLength (m+1))]
    with ω hsource hreceiver
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let L := q3ModelLength (m+1)
  let F := fun p (_U : OldSignedCellIndex Q 134) => oldHessianFullModeColumn Q 133 M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L p
  let G := oldHessianMinusOscillationColumn Q 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L
  have hFs := old_hessian_full_mode_series (m+129) 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L
  have hh := old_hessian_broken_mode_pairing Q 134 G F
    (fun p U i => old_hessian_minus_oscillation_column_memLp Q 134 M.nu (Annealed.sigmaBar M m)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L p U i)
    (fun p U i => (old_hessian_full_mode_regular (m+129) 133 M.nu (Annealed.sigmaBar M m)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L p U i).1)
    (fun p U i => (old_hessian_full_mode_regular (m+129) 133 M.nu (Annealed.sigmaBar M m)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L p U i).2)
    hreceiver.1 hFs.1
  have hs := hsource b L
  have hScap : (∑' p,oldHessianFullModeEnergy Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L p)≤oldHessianSourceEnvelope M m b L ω :=
    hFs.2.trans_le hs.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact (mul_le_mul (Real.sqrt_le_sqrt hreceiver.2) (Real.sqrt_le_sqrt hScap)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq (mul_comm _ _)

end
end ASDExplicitGamma.Scalar
