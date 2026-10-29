module

public import ASDExplicitGamma.Native.OldSignedSpectralWhite
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Reflection of the actual q3 spectral measure. The reflection combined
with conjugation characterizes the real physical white-mode fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model
noncomputable section

/-- The q3 characteristic function with the frequency convention used by
Mathlib, as distinct from the 2*pi Fourier convention of the source. -/
theorem old_signed_spectral_charFun (b : ℝ) (t : Q3FrequencyPlane) :
    charFun (q3SpectralMeasure b) t =
      (b^2*q3Cov (t.fst/(2*Real.pi))*q3Cov (t.snd/(2*Real.pi)):ℝ) := by
  have hh := q3SpectralMeasure_exponential_integral b (t.fst/(2*Real.pi)) (t.snd/(2*Real.pi))
  have he (xi : Q3FrequencyPlane) :
      2*Real.pi*(xi.fst*(t.fst/(2*Real.pi))+xi.snd*(t.snd/(2*Real.pi))) = inner ℝ xi t := by
    simp only [WithLp.prod_inner_apply,RCLike.inner_apply,conj_trivial,
      WithLp.ofLp_fst,WithLp.ofLp_snd]
    field_simp [Real.pi_ne_zero]
  simp_rw [he] at hh
  simpa only [charFun_apply] using hh

/-- Reflection invariance is proved from the actual characteristic function;
no unproved even-density or realization assumption is supplied. -/
theorem old_signed_spectral_measure_neg (b : ℝ) :
    (q3SpectralMeasure b).map (fun xi => -xi) = q3SpectralMeasure b := by
  apply Measure.ext_of_charFun
  funext t
  have hh := charFun_map_smul (μ := q3SpectralMeasure b) (-1:ℝ) t
  simp only [neg_one_smul] at hh
  rw [hh,old_signed_spectral_charFun,old_signed_spectral_charFun]
  simp only [WithLp.neg_fst,WithLp.neg_snd,neg_div,q3Cov_even]

/-- The same reflection as a measure-preserving map, for constructing the
continuous involution on spectral L2 rather than manipulating representatives. -/
theorem old_signed_spectral_neg_measurePreserving (b : ℝ) :
    MeasurePreserving (fun xi : Q3FrequencyPlane => -xi)
      (q3SpectralMeasure b) (q3SpectralMeasure b) :=
  ⟨measurable_neg,old_signed_spectral_measure_neg b⟩

/-- Frequency reflection on the actual spectral L2 carrier. -/
def oldSignedSpectralReflect (b : ℝ) :
    Lp ℂ 2 (q3SpectralMeasure b) →ₗᵢ[ℂ] Lp ℂ 2 (q3SpectralMeasure b) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun xi : Q3FrequencyPlane => -xi)
    (old_signed_spectral_neg_measurePreserving b)

/-- Pointwise characterization of reflection, with its measure-preserving
hypothesis already proved for the actual measure. -/
theorem old_signed_spectral_reflect_coeFn (b : ℝ) (f : Lp ℂ 2 (q3SpectralMeasure b)) :
    (oldSignedSpectralReflect b f : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      fun xi => f (-xi) :=
  Lp.coeFn_compMeasurePreserving f (old_signed_spectral_neg_measurePreserving b)

end
end ASDExplicitGamma.Native
