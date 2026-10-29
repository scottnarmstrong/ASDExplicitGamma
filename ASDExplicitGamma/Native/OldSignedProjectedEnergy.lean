module

public import ASDExplicitGamma.Native.OldSignedWhiteContraction

/-! Exact full-mode energy of the physical whole-plane projected kernels.
Reality and the spectral isometry preserve all energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- Complexification of real white noise preserves its energy exactly. -/
theorem old_signed_white_complexify_norm_sq (f : WhiteNoise) :
    ‖oldSignedWhiteComplexify f‖^2=‖f‖^2 := by
  calc
    _ = (inner ℂ (oldSignedWhiteComplexify f) (oldSignedWhiteComplexify f)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := by
      rw [old_signed_white_complexify_inner,real_inner_self_eq_norm_sq,Complex.ofReal_re]

/-- The ordinary complex L2 norm is the integral of squared pointwise norms. -/
theorem old_signed_complex_L2_norm_sq {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : Lp ℂ 2 mu) : ‖f‖^2=∫ x,‖f x‖^2 ∂mu := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,←integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  apply integral_congr_ae
  filter_upwards with x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

/-- Every matrix-entry square is integrable for the actual q3 spectral
measure, proved from the genuine filtered-character L2 membership. -/
theorem old_signed_helmholtz_square_integrable (b : ℝ) (i j : Fin 2) :
    Integrable (fun xi => oldSignedHelmholtzEntry xi i j^2) (q3SpectralMeasure b) := by
  have hp := old_signed_projected_character_memLp b 0 i j
  have hi := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  simpa [oldSignedProjectedCharacterValue,norm_mul,Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real,Real.norm_eq_abs,sq_abs] using hi

/-- The actual real projected-kernel energy is the exact multiplier-square
integral, with no loss from taking the real white representative. -/
theorem old_signed_projected_white_energy (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    ‖oldSignedProjectedWhiteKernel b L x i j‖^2 =
      ∫ xi,oldSignedHelmholtzEntry xi i j^2 ∂q3SpectralMeasure b := by
  rw [←old_signed_white_complexify_norm_sq,old_signed_projected_white_kernel_complexify,
    LinearIsometry.norm_map,old_signed_complex_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [old_signed_projected_character_coeFn b x i j] with xi hx
  rw [hx]
  rw [oldSignedProjectedCharacterValue,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- The Frobenius energy of the Helmholtz matrix is its trace, including
at zero frequency under the canonical zero convention. -/
theorem old_signed_helmholtz_square_sum (xi : Q3FrequencyPlane) :
    (∑ i : Fin 2,∑ j : Fin 2,oldSignedHelmholtzEntry xi i j^2)=
      oldSignedHelmholtzEntry xi 0 0+oldSignedHelmholtzEntry xi 1 1 := by
  by_cases hz : xi.fst^2+xi.snd^2=0
  · simp [oldSignedHelmholtzEntry,oldSignedFrequency,hz]
  · norm_num [oldSignedHelmholtzEntry,oldSignedFrequency,Fin.sum_univ_two]
    field_simp [hz]

/-- Summing both loads and both components of the actual projected kernels
gives exactly one shell variance, at every spatial point. -/
theorem old_signed_projected_white_total_energy (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) : (∑ i : Fin 2,∑ j : Fin 2,‖oldSignedProjectedWhiteKernel b L x i j‖^2)=b^2 := by
  simp_rw [old_signed_projected_white_energy]
  have hs (i : Fin 2) : (∑ j : Fin 2,∫ xi,oldSignedHelmholtzEntry xi i j^2 ∂q3SpectralMeasure b) =
      ∫ xi,∑ j : Fin 2,oldSignedHelmholtzEntry xi i j^2 ∂q3SpectralMeasure b :=
    (integral_finsetSum _ (fun j _ => old_signed_helmholtz_square_integrable b i j)).symm
  simp_rw [hs]
  rw [←integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => old_signed_helmholtz_square_integrable b i j))]
  simp_rw [old_signed_helmholtz_square_sum]
  have hi (i j : Fin 2) : Integrable (fun xi => oldSignedHelmholtzEntry xi i j)
      (q3SpectralMeasure b) := by
    have hp := old_signed_projected_character_memLp b 0 i j
    have hr := Complex.reCLM.comp_memLp' hp
    convert hr.integrable (by norm_num) using 1
    funext xi
    simp [oldSignedProjectedCharacterValue,Complex.reCLM_apply]
  rw [integral_add (hi 0 0) (hi 1 1),old_signed_helmholtz_entry_integral,
    old_signed_helmholtz_entry_integral]
  norm_num

end
end ASDExplicitGamma.Native
