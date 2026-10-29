module

public import ASDExplicitGamma.Native.OldSignedSpectralReflection

/-! Compatibility of spectral reflection/conjugation with real physical
white kernels. No realness of a projected covariance mode is assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ComplexConjugate
noncomputable section

/-- Conjugation as a continuous real-linear map on an actual L2 space. -/
def oldSignedConjugate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 μ

/-- Conjugation acts on the actual L2 representative. -/
theorem old_signed_conjugate_coeFn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Lp ℂ 2 μ) :
    (oldSignedConjugate μ f : Ω → ℂ) =ᵐ[μ] fun w => conj (f w) := by
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL f

/-- The continuous conjugation map has the required conjugate scalar rule. -/
theorem old_signed_conjugate_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : ℂ) (f : Lp ℂ 2 μ) :
    oldSignedConjugate μ (c • f) = conj c • oldSignedConjugate μ f := by
  apply Lp.ext
  filter_upwards [old_signed_conjugate_coeFn μ (c • f),old_signed_conjugate_coeFn μ f,
    Lp.coeFn_smul c f,Lp.coeFn_smul (conj c) (oldSignedConjugate μ f)] with w ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha,hd,hc,hb]
  exact map_mul _ _ _

/-- Reflection followed by conjugation is the reality operation for the
source's Fourier convention. -/
def oldSignedSpectralReality (b : ℝ) :
    Lp ℂ 2 (q3SpectralMeasure b) →L[ℝ] Lp ℂ 2 (q3SpectralMeasure b) :=
  (oldSignedConjugate (q3SpectralMeasure b)).comp
    ((oldSignedSpectralReflect b).toContinuousLinearMap.restrictScalars ℝ)

/-- The actual spectral reality operation on representatives. -/
theorem old_signed_spectral_reality_coeFn (b : ℝ) (f : Lp ℂ 2 (q3SpectralMeasure b)) :
    (oldSignedSpectralReality b f : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      fun xi => conj (f (-xi)) := by
  filter_upwards [old_signed_conjugate_coeFn (q3SpectralMeasure b) (oldSignedSpectralReflect b f),
    old_signed_spectral_reflect_coeFn b f] with xi hc hr
  exact hc.trans (congrArg conj hr)

/-- Reality conjugates complex coefficients, while retaining the same
physical spatial character. -/
theorem old_signed_spectral_reality_smul (b : ℝ) (c : ℂ) (f : Lp ℂ 2 (q3SpectralMeasure b)) :
    oldSignedSpectralReality b (c • f) = conj c • oldSignedSpectralReality b f := by
  change oldSignedConjugate _ (oldSignedSpectralReflect b (c • f)) = _
  rw [map_smul,old_signed_conjugate_smul]
  rfl

/-- Every spatial character is fixed by spectral reality. -/
theorem old_signed_spectral_reality_character (b : ℝ) (x : Vec 2) :
    oldSignedSpectralReality b (q3SpectralCharacter b (q3SpectralPoint x)) =
      q3SpectralCharacter b (q3SpectralPoint x) := by
  apply Lp.ext
  have he := q3SpectralCharacter_coeFn b (q3SpectralPoint x)
  have hn := (old_signed_spectral_neg_measurePreserving b).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [old_signed_spectral_reality_coeFn b _,he,hn] with xi hr hx hn
  dsimp only [Function.comp_def] at hn
  rw [hr,hn,hx,←Complex.exp_conj]
  congr 1
  simp only [WithLp.neg_fst,WithLp.neg_snd,map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

/-- The actual q3 white kernels are real, independently of spectral data. -/
theorem old_signed_white_section_real (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    oldSignedConjugate volume (oldSignedComplexWhiteSection b L x) = oldSignedComplexWhiteSection b L x := by
  apply Lp.ext
  filter_upwards [old_signed_conjugate_coeFn volume (oldSignedComplexWhiteSection b L x),
    Complex.ofRealCLM.coeFn_compLpL (q3Section b L h3Zero (L.1 • x))] with w hc hr
  change oldSignedComplexWhiteSection b L x w = _ at hr
  rw [hc,hr]
  simp only [Complex.ofRealCLM_apply,Complex.conj_ofReal]

/-- The spectral-to-white isometry intertwines the two reality operations.
Density supplies this identity beyond finite trigonometric polynomials. -/
theorem old_signed_spectral_white_reality (b : ℝ) (L : {l : ℝ // 0 < l})
    (f : Lp ℂ 2 (q3SpectralMeasure b)) :
    oldSignedSpectralWhiteInverse b L (oldSignedSpectralReality b f) =
      oldSignedConjugate volume (oldSignedSpectralWhiteInverse b L f) := by
  let U := oldSignedSpectralWhiteInverse b L
  apply DenseRange.induction_on (q3SpectralCombination_dense b)
    (p := fun g => U (oldSignedSpectralReality b g) = oldSignedConjugate volume (U g)) f
  · exact isClosed_eq (U.continuous.comp (oldSignedSpectralReality b).continuous)
      ((oldSignedConjugate volume).continuous.comp U.continuous)
  · intro c
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,
      old_signed_spectral_reality_smul,old_signed_spectral_reality_character,
      LinearIsometry.map_smul,old_signed_conjugate_smul]
    simp only [U,old_signed_spectral_white_character,old_signed_white_section_real]

end
end ASDExplicitGamma.Native
