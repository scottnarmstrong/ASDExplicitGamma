module

public import ASDExplicitGamma.Native.OldSignedProjectedPointDerivative

/-! The actual L2 spatial-derivative multiplier of each projected kernel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- One spatial component of the exact projected-character derivative. -/
def oldSignedProjectedDerivativeValue (x : Vec 2) (i j k : Fin 2) (xi : Q3FrequencyPlane) : ℂ :=
  (((2*Real.pi*oldSignedFrequency xi k:ℝ):ℂ)*I)*oldSignedProjectedCharacterValue x i j xi

/-- The derivative multiplier is bounded by its actual first-frequency
majorant, uniformly over the projection entries. -/
theorem old_signed_projected_derivative_value_norm (x : Vec 2) (i j k : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedProjectedDerivativeValue x i j k xi‖ ≤ 2*Real.pi*|oldSignedFrequency xi k| := by
  rw [oldSignedProjectedDerivativeValue,norm_mul,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
  exact (mul_le_mul_of_nonneg_left (old_signed_projected_character_value_norm x i j xi)
    (by positivity)).trans_eq (mul_one _)

/-- Spatial differentiation does not leave the actual L2 spectral space.
The graph moment supplies rather than assumes the needed integrability. -/
theorem old_signed_projected_derivative_memLp (b : ℝ) (x : Vec 2) (i j k : Fin 2) :
    MemLp (oldSignedProjectedDerivativeValue x i j k) 2 (q3SpectralMeasure b) := by
  have hm : AEStronglyMeasurable (fun xi : Q3FrequencyPlane => oldSignedFrequency xi k)
      (q3SpectralMeasure b) := (q3FrequencyCoordinate_continuous k).aestronglyMeasurable
  have hp := (old_signed_projected_character_memLp b x i j).aestronglyMeasurable
  apply (((old_signed_frequency_memLp b k).norm).const_mul (2*Real.pi)).mono'
  · fun_prop [oldSignedProjectedDerivativeValue]
  · filter_upwards [] with xi
    simpa only [Real.norm_eq_abs] using old_signed_projected_derivative_value_norm x i j k xi

/-- The full derivative multiplier, without a finite-frequency cutoff. -/
def oldSignedProjectedDerivative (b : ℝ) (x : Vec 2) (i j k : Fin 2) : Lp ℂ 2 (q3SpectralMeasure b) :=
  (old_signed_projected_derivative_memLp b x i j k).toLp _

/-- Exact formula for its L2 representative. -/
theorem old_signed_projected_derivative_coeFn (b : ℝ) (x : Vec 2) (i j k : Fin 2) :
    (oldSignedProjectedDerivative b x i j k : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      oldSignedProjectedDerivativeValue x i j k :=
  (old_signed_projected_derivative_memLp b x i j k).coeFn_toLp

/-- The spatial derivative assembled as a genuine bounded linear map. -/
def oldSignedProjectedSpatialDerivative (b : ℝ) (x : Vec 2) (i j : Fin 2) :
    Vec 2 →L[ℝ] Lp ℂ 2 (q3SpectralMeasure b) :=
  (ContinuousLinearMap.proj 0).smulRight (oldSignedProjectedDerivative b x i j 0)+
    (ContinuousLinearMap.proj 1).smulRight (oldSignedProjectedDerivative b x i j 1)

/-- The bounded derivative has the exact pointwise Fourier derivative,
for every spatial increment. -/
theorem old_signed_projected_spatial_derivative_coeFn (b : ℝ) (x v : Vec 2) (i j : Fin 2) :
    (oldSignedProjectedSpatialDerivative b x i j v : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      fun xi => oldSignedProjectedPointDerivative x i j xi v := by
  change ((v 0:ℝ) • oldSignedProjectedDerivative b x i j 0+
    (v 1:ℝ) • oldSignedProjectedDerivative b x i j 1 : Lp ℂ 2 (q3SpectralMeasure b)) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add ((v 0:ℝ) • oldSignedProjectedDerivative b x i j 0)
    ((v 1:ℝ) • oldSignedProjectedDerivative b x i j 1),
    Lp.coeFn_smul (v 0:ℝ) (oldSignedProjectedDerivative b x i j 0),
    Lp.coeFn_smul (v 1:ℝ) (oldSignedProjectedDerivative b x i j 1),
    old_signed_projected_derivative_coeFn b x i j 0,
    old_signed_projected_derivative_coeFn b x i j 1] with xi ha h0 h1 hc0 hc1
  simp only [Pi.add_apply] at ha
  simp only [Pi.smul_apply] at h0 h1
  rw [ha,h0,h1,hc0,hc1]
  simp only [oldSignedProjectedPointDerivative,smul_apply,oldSignedPhaseDerivative,add_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    oldSignedProjectedDerivativeValue,oldSignedFrequency,Fin.isValue,ite_true]
  norm_num only [show (1:Fin 2)≠0 by decide,ite_false]
  simp only [Complex.real_smul]
  push_cast
  ring

end
end ASDExplicitGamma.Native
