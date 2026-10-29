module

public import ASDExplicitGamma.Model.SpectralFirstChaosIsometry
public import ASDExplicitGamma.Gaussian.Q3KernelCovariance

/-! The q3 spectral model embedded in the actual complexified white-noise
space. This identifies projected mode covariances on the same realization
as the OLD coefficient directions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped RealInnerProductSpace
noncomputable section

/-- Complexification of the actual real white-noise kernel space. -/
def oldSignedWhiteComplexify : WhiteNoise →L[ℝ] Lp ℂ 2 (volume : Measure (Vec 2)) :=
  Complex.ofRealCLM.compLpL 2 volume

/-- A spatially translated physical q3 kernel in complex white noise.
The coordinate x is measured in shell-length units. -/
def oldSignedComplexWhiteSection (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    Lp ℂ 2 (volume : Measure (Vec 2)) :=
  oldSignedWhiteComplexify (q3Section b L h3Zero (L.1 • x))

/-- Complexification preserves the real white-noise covariance exactly. -/
theorem old_signed_white_complexify_inner (f g : WhiteNoise) :
    inner ℂ (oldSignedWhiteComplexify f) (oldSignedWhiteComplexify g) = (inner ℝ f g:ℂ) := by
  unfold oldSignedWhiteComplexify
  rw [L2.inner_def]
  calc
    _ = ∫ w : Vec 2, ((f w*g w:ℝ):ℂ) := by
      apply integral_congr_ae
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL f,Complex.ofRealCLM.coeFn_compLpL g] with w hf hg
      rw [hf,hg]
      simp only [Complex.ofRealCLM_apply,RCLike.inner_apply,Complex.conj_ofReal,Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [integral_complex_ofReal,L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Real.inner_apply]

/-- The physical white sections and the spectral characters have the same
Gram kernel, including amplitude and spatial-length normalization. -/
theorem old_signed_white_section_inner (b : ℝ) (L : {l : ℝ // 0 < l}) (x y : Vec 2) :
    inner ℂ (oldSignedComplexWhiteSection b L x) (oldSignedComplexWhiteSection b L y) =
      inner ℂ (q3SpectralCharacter b (q3SpectralPoint x))
        (q3SpectralCharacter b (q3SpectralPoint y)) := by
  rw [oldSignedComplexWhiteSection,oldSignedComplexWhiteSection,old_signed_white_complexify_inner,
    q3Section_covariance,q3SpectralCharacter_inner]
  have h0 : ((L.1 • x) 0-(L.1 • y) 0)/L.1=x 0-y 0 := by
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp [L.2.ne']
  have h1 : ((L.1 • x) 1-(L.1 • y) 1)/L.1=x 1-y 1 := by
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp [L.2.ne']
  rw [h0,h1]
  simp only [q3SpectralPoint,WithLp.toLp_fst,WithLp.toLp_snd]
  rw [show y 0-x 0=-(x 0-y 0) by ring,show y 1-x 1=-(x 1-y 1) by ring,
    q3Cov_even,q3Cov_even]

/-- Equality of Gram kernels extends to every finite complex combination. -/
theorem old_signed_white_combination_norm (b : ℝ) (L : {l : ℝ // 0 < l}) (c : Vec 2 →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (oldSignedComplexWhiteSection b L) c‖ =
      ‖Finsupp.linearCombination ℂ (fun x => q3SpectralCharacter b (q3SpectralPoint x)) c‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),Finsupp.linearCombination_apply,
    Finsupp.sum_inner,Finsupp.inner_sum,inner_smul_left,inner_smul_right,old_signed_white_section_inner]

/-- The spectral-to-white isometry is constructed from the actual q3 kernel,
not from an assumed covariance-factor equivalence. -/
def oldSignedSpectralWhiteInverse (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Lp ℂ 2 (q3SpectralMeasure b) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec 2)) :=
  (Finsupp.linearCombination ℂ (oldSignedComplexWhiteSection b L)).extendOfIsometry
    (e := Finsupp.linearCombination ℂ (fun x : Vec 2 => q3SpectralCharacter b (q3SpectralPoint x)))
    (q3SpectralCombination_dense b) (old_signed_white_combination_norm b L)

/-- Each spectral character maps to the same physical kernel whose real
basis coefficients are the actual q3 convolution directions. -/
theorem old_signed_spectral_white_character (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    oldSignedSpectralWhiteInverse b L (q3SpectralCharacter b (q3SpectralPoint x)) =
      oldSignedComplexWhiteSection b L x := by
  have hh := LinearMap.extendOfIsometry_eq
    (Finsupp.linearCombination ℂ (oldSignedComplexWhiteSection b L))
    (e := Finsupp.linearCombination ℂ (fun x : Vec 2 => q3SpectralCharacter b (q3SpectralPoint x)))
    (q3SpectralCombination_dense b) (old_signed_white_combination_norm b L) (Finsupp.single x 1)
  simpa only [oldSignedSpectralWhiteInverse,Finsupp.linearCombination_single,one_smul] using hh

end
end ASDExplicitGamma.Native
