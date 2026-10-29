module

public import ASDExplicitGamma.Native.OldSignedSpectralProjectedModes

/-! Actual real white-noise kernels for the whole-plane projected loads.
Realness follows from the spectral multiplier, not from a new assumption. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ComplexConjugate
noncomputable section

/-- Real part of a complex white-noise kernel as a bounded real-linear map. -/
def oldSignedWhiteRealPart : Lp ℂ 2 (volume : Measure (Vec 2)) →L[ℝ] WhiteNoise :=
  Complex.reCLM.compLpL 2 volume

/-- The real part has its ordinary pointwise representative. -/
theorem old_signed_white_real_part_coeFn (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    (oldSignedWhiteRealPart f : Vec 2 → ℝ) =ᵐ[volume] fun w => (f w).re :=
  Complex.reCLM.coeFn_compLpL f

/-- A conjugation-fixed complex kernel is exactly the complexification of
its real part. Thus taking the real part does not lose energy or covariance. -/
theorem old_signed_white_complexify_real_part (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (hf : oldSignedConjugate volume f=f) :
    oldSignedWhiteComplexify (oldSignedWhiteRealPart f)=f := by
  apply Lp.ext
  have hc := old_signed_conjugate_coeFn volume f
  rw [hf] at hc
  filter_upwards [hc,old_signed_white_real_part_coeFn f,
    Complex.ofRealCLM.coeFn_compLpL (oldSignedWhiteRealPart f)] with w hc hr he
  change oldSignedWhiteComplexify (oldSignedWhiteRealPart f) w = _ at he
  rw [he,hr]
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · change 0=(f w).im
    linarith only [hi]

/-- The projected physical kernel at dimensionless spatial point x.
Physical coordinates are L*x, as in oldSignedComplexWhiteSection. -/
def oldSignedProjectedWhiteKernel (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) : WhiteNoise :=
  oldSignedWhiteRealPart (oldSignedSpectralWhiteInverse b L (oldSignedProjectedCharacter b x i j))

/-- The projected white kernel is the entire spectral projection image;
no imaginary part or high-frequency component has been discarded. -/
theorem old_signed_projected_white_kernel_complexify (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    oldSignedWhiteComplexify (oldSignedProjectedWhiteKernel b L x i j) =
      oldSignedSpectralWhiteInverse b L (oldSignedProjectedCharacter b x i j) := by
  apply old_signed_white_complexify_real_part
  simpa only [old_signed_projected_character_real] using
    (old_signed_spectral_white_reality b L (oldSignedProjectedCharacter b x i j)).symm

/-- The physical and projected white covariance is the exact spectral
Helmholtz matrix entry, with no basis or projection premise. -/
theorem old_signed_projected_white_covariance (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    inner ℝ (q3Section b L h3Zero (L.1 • x)) (oldSignedProjectedWhiteKernel b L x i j) =
      ∫ xi, oldSignedHelmholtzEntry xi i j ∂q3SpectralMeasure b := by
  apply Complex.ofReal_injective
  calc
    _ = inner ℂ (oldSignedComplexWhiteSection b L x)
        (oldSignedWhiteComplexify (oldSignedProjectedWhiteKernel b L x i j)) :=
      (old_signed_white_complexify_inner _ _).symm
    _ = inner ℂ (q3SpectralCharacter b (q3SpectralPoint x))
        (oldSignedProjectedCharacter b x i j) := by
      rw [old_signed_projected_white_kernel_complexify,←old_signed_spectral_white_character,
        LinearIsometry.inner_map_map]
    _ = _ := by
      rw [L2.inner_def,←integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards [q3SpectralCharacter_coeFn b (q3SpectralPoint x),
        old_signed_projected_character_coeFn b x i j] with xi hc hp
      rw [hc,hp]
      dsimp only [oldSignedProjectedCharacterValue]
      simp only [q3SpectralPoint,WithLp.toLp_fst,WithLp.toLp_snd]
      rw [RCLike.inner_apply]
      calc
        _ = (oldSignedHelmholtzEntry xi i j:ℂ)*
            (exp (((2*Real.pi*(xi.fst*x 0+xi.snd*x 1):ℝ):ℂ)*I)*
              conj (exp (((2*Real.pi*(xi.fst*x 0+xi.snd*x 1):ℝ):ℂ)*I))) := by ring
        _ = _ := by
          rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.norm_exp_ofReal_mul_I]
          norm_num

end
end ASDExplicitGamma.Native
