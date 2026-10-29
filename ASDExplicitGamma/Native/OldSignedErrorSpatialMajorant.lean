module

public import ASDExplicitGamma.Native.OldSignedFlatSpatialMajorant
public import ASDExplicitGamma.Native.OldSignedSourceMixedMajorant
public import ASDExplicitGamma.Native.OldSignedDerivativeSpatialMajorant
public import ASDExplicitGamma.Native.OldSignedQ1ErrorPayment
public import ASDExplicitGamma.Native.OldSignedDirectionalErrorBill

/-! Full source-derived spatial/annealed majorant of the actual AN error. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The complete literal AN directional error is below the four-block
integrable envelope almost surely, with every OLD history and source term
kept in the physical parent frame. -/
theorem old_signed_actual_error_spatial_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      descendantsAverage (originCube 2 n) r (fun U => oldSignedDirectionalCellError (originCube 2 n) U r
        M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (oldSignedPartialResponseCoefficient n 1 t ω) b L)≤oldSignedActualErrorEnvelope M n r t b L ω := by
  have hf := old_signed_actual_flat_spatial_majorant M h hM hg n hpast r hr t ht b L
  have hs := old_signed_actual_source_mixed_majorant M h hM hg n hpast r hr t ht b L
  have hd := old_signed_actual_derivative_spatial_majorant M h hM hg n hpast r hr t ht b L
  filter_upwards [hf,hs,hd] with ω hfω hsω hdω
  have hb := old_signed_actual_boundary_spatial_payment M n r t ht ω b L
  have hall := add_le_add (add_le_add (add_le_add hfω hsω) hdω) hb
  dsimp only at hall
  rw [←descendantsAverage_add,←descendantsAverage_add,←descendantsAverage_add] at hall
  refine le_trans ?_ hall
  apply le_of_eq
  unfold oldSignedDirectionalCellError oldSignedDirectionalErrorBill descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  dsimp only [oldSignedPartialFrameField]
  ring

/-- The physical q1 error has a source-derived integrable dominating
function with the complete four-block first-moment bound. This avoids any
implicit assumption of integrability of a raw real-valued history. -/
theorem old_signed_q1_error_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualErrorEnvelope M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualErrorEnvelope M n 5 t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤oldSignedQ1ErrorCap M n t b L ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      descendantsAverage (originCube 2 n) 5 (fun U => oldSignedDirectionalCellError (originCube 2 n) U 5
        M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (oldSignedPartialResponseCoefficient n 1 t ω) b L)≤oldSignedActualErrorEnvelope M n 5 t b L ω) := by
  have hh := old_signed_q1_error_payment M h hM hg n hpast t ht b L
  exact ⟨hh.1,hh.2,old_signed_actual_error_spatial_majorant M h hM hg n
    (fun l hl => hpast l hl.le) 5 (by norm_num) t ht b L⟩

end
end ASDExplicitGamma.Native
