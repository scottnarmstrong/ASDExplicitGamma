module

public import ASDExplicitGamma.Native.OldSignedPotentialStrongDerivative
public import ASDExplicitGamma.Native.OldSignedStrongContinuity
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Continuity of the complete projected characters gives C1 regularity of
the actual local potential, rather than an assumed gradient representative. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- Projected characters are uniformly bounded by one at each frequency. -/
theorem old_signed_projected_character_value_norm (x : Vec 2) (i j : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedProjectedCharacterValue x i j xi‖≤1 := by
  rw [oldSignedProjectedCharacterValue,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  exact old_signed_helmholtz_entry_abs xi i j

/-- The complete Helmholtz character depends strongly continuously on the
spatial point. The finite spectral measure controls all frequencies at once. -/
theorem old_signed_projected_character_continuous (b : ℝ) (i j : Fin 2) :
    Continuous (fun x : Vec 2 => oldSignedProjectedCharacter b x i j) := by
  let B : Lp ℝ 2 (q3SpectralMeasure b) :=
    (memLp_const (1:ℝ) : MemLp (fun _ : Q3FrequencyPlane => (1:ℝ)) 2 (q3SpectralMeasure b)).toLp _
  apply old_signed_continuous_L2 (q3SpectralMeasure b)
    (fun x => oldSignedProjectedCharacter b x i j) (fun x => oldSignedProjectedCharacterValue x i j) B
    (fun x => old_signed_projected_character_coeFn b x i j)
  · apply Filter.Eventually.of_forall
    intro xi
    unfold oldSignedProjectedCharacterValue
    fun_prop
  · intro x
    have hB : (B : Q3FrequencyPlane → ℝ) =ᵐ[q3SpectralMeasure b] fun _ => (1:ℝ) :=
      (memLp_const (1:ℝ) : MemLp (fun _ : Q3FrequencyPlane => (1:ℝ)) 2 (q3SpectralMeasure b)).coeFn_toLp
    filter_upwards [hB] with xi hB
    rw [hB,norm_one]
    exact old_signed_projected_character_value_norm x i j xi

/-- The full derivative field is continuous as a bounded linear map, not
merely coordinatewise as a scalar multiplier. -/
theorem old_signed_spectral_potential_derivative_continuous (b : ℝ) (j : Fin 2) :
    Continuous (fun x : Vec 2 => oldSignedSpectralPotentialDerivative b x j) := by
  have h0 := (ContinuousLinearMap.smulRightL ℝ (Vec 2) (Lp ℂ 2 (q3SpectralMeasure b))
    (ContinuousLinearMap.proj 0)).continuous.comp (old_signed_projected_character_continuous b 0 j)
  have h1 := (ContinuousLinearMap.smulRightL ℝ (Vec 2) (Lp ℂ 2 (q3SpectralMeasure b))
    (ContinuousLinearMap.proj 1)).continuous.comp (old_signed_projected_character_continuous b 1 j)
  exact h0.add h1

/-- The actual local potential is C1 in its physical spatial variable. -/
theorem old_signed_spectral_potential_contDiff (b : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (fun x : Vec 2 => oldSignedSpectralPotential b x j) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨_,old_signed_spectral_potential_derivative_continuous b j,
    fun x => old_signed_spectral_potential_hasFDerivAt b x j⟩

end
end ASDExplicitGamma.Native
