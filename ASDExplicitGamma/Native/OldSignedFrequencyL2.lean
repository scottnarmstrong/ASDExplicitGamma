module

public import ASDExplicitGamma.Native.OldSignedPotentialRegularity

/-! Actual square-integrable frequency majorants for spatial derivatives
of the complete projected q3 characters. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- Each coordinate has finite second moment under the actual q3 spectral
measure, supplied by its previously proved graph-weight integrability. -/
theorem old_signed_frequency_memLp (b : ℝ) (i : Fin 2) :
    MemLp (fun xi : Q3FrequencyPlane => oldSignedFrequency xi i) 2 (q3SpectralMeasure b) := by
  have hm : AEStronglyMeasurable (fun xi : Q3FrequencyPlane => oldSignedFrequency xi i)
      (q3SpectralMeasure b) := (q3FrequencyCoordinate_continuous i).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (q3SpectralMeasure_graphWeight_integrable b).mono' (hm.norm.pow 2)
  filter_upwards [] with xi
  simpa only [Pi.pow_apply,Real.norm_of_nonneg (sq_nonneg _),Real.norm_eq_abs,sq_abs,
    oldSignedFrequency,q3FrequencyCoordinate] using
    q3FrequencyCoordinate_sq_le i xi

/-- This actual L2 envelope dominates all normalized remainders of the
projected character's spatial derivatives. -/
theorem old_signed_frequency_envelope_memLp (b : ℝ) :
    MemLp (fun xi : Q3FrequencyPlane =>
      4*Real.pi*(|oldSignedFrequency xi 0|+|oldSignedFrequency xi 1|)) 2 (q3SpectralMeasure b) := by
  simpa only [Real.norm_eq_abs,Pi.add_apply] using
    (((old_signed_frequency_memLp b 0).norm).add ((old_signed_frequency_memLp b 1).norm)).const_mul (4*Real.pi)

/-- The common envelope as a genuine finite L2 function. -/
def oldSignedFrequencyEnvelope (b : ℝ) : Lp ℝ 2 (q3SpectralMeasure b) :=
  (old_signed_frequency_envelope_memLp b).toLp _

/-- Exact representative of the complete frequency envelope. -/
theorem old_signed_frequency_envelope_coeFn (b : ℝ) :
    (oldSignedFrequencyEnvelope b : Q3FrequencyPlane → ℝ) =ᵐ[q3SpectralMeasure b]
      fun xi => 4*Real.pi*(|oldSignedFrequency xi 0|+|oldSignedFrequency xi 1|) :=
  (old_signed_frequency_envelope_memLp b).coeFn_toLp

end
end ASDExplicitGamma.Native
