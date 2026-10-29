module

public import ASDExplicitGamma.Native.OldSignedPotentialBounds

/-! The whole-plane projected potential difference is genuine spectral L2,
including the low-frequency region. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- The potential difference has finite second moment for every spatial
point. Its frequency bound depends only on that point's two coordinates. -/
theorem old_signed_potential_memLp (b : ℝ) (x : Vec 2) (j : Fin 2) :
    MemLp (oldSignedPotentialValue x j) 2 (q3SpectralMeasure b) := by
  apply MemLp.of_bound (C := |x 0|+|x 1|)
  · apply Measurable.aestronglyMeasurable
    have hc : Measurable (fun xi : Q3FrequencyPlane => oldSignedFrequency xi j) := by
      unfold oldSignedFrequency
      split_ifs <;> fun_prop
    have hnum : Measurable (fun xi : Q3FrequencyPlane => (oldSignedFrequency xi j:ℂ)) := hc.complex_ofReal
    exact (hnum.div (by fun_prop)).mul (by fun_prop)
  · exact Filter.Eventually.of_forall (old_signed_potential_value_norm x j)

/-- The potential difference as an actual L2 element, with no assumed
inverse-gradient integrability at frequency zero. -/
def oldSignedSpectralPotential (b : ℝ) (x : Vec 2) (j : Fin 2) : Lp ℂ 2 (q3SpectralMeasure b) :=
  (old_signed_potential_memLp b x j).toLp _

/-- Exact pointwise formula for the complete potential difference. -/
theorem old_signed_spectral_potential_coeFn (b : ℝ) (x : Vec 2) (j : Fin 2) :
    (oldSignedSpectralPotential b x j : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      oldSignedPotentialValue x j :=
  (old_signed_potential_memLp b x j).coeFn_toLp

end
end ASDExplicitGamma.Native
