module

public import ASDExplicitGamma.Main.PathwiseHessianLocalizedCovariance
public import ASDExplicitGamma.Native.OldSignedWhiteContraction
public import ASDExplicitGamma.Model.Q3DerivativeSmooth
public import Mathlib.Analysis.Complex.OperatorNorm

/-! Uniform norm bounds for the actual OLD-frame projected q3 white kernels. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Complex ASDExplicitGamma.Model ASDExplicitGamma.Response
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Native

/-- Complexification preserves the real white-noise L² norm. -/
theorem main_old_signed_white_complexify_norm (f : WhiteNoise) :
    ‖oldSignedWhiteComplexify f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),
    norm_sq_eq_re_inner (𝕜 := ℝ), old_signed_white_complexify_inner]
  rfl

/-- The projected spectral character has a spatially constant L² norm because
the Helmholtz multiplier has modulus independent of the character phase. -/
private theorem main_old_signed_projected_character_value_norm
    (x : Vec 2) (i j : Fin 2) (ξ : Q3FrequencyPlane) :
    ‖oldSignedProjectedCharacterValue x i j ξ‖ =
      |oldSignedHelmholtzEntry ξ i j| := by
  rw [oldSignedProjectedCharacterValue, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem main_old_signed_projected_character_norm_eq
    (b : ℝ) (x y : Vec 2) (i j : Fin 2) :
    ‖oldSignedProjectedCharacter b x i j‖ =
      ‖oldSignedProjectedCharacter b y i j‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
    (Lp.aestronglyMeasurable _)
  filter_upwards [old_signed_projected_character_coeFn b x i j,
    old_signed_projected_character_coeFn b y i j] with ξ hx hy
  rw [hx, hy, main_old_signed_projected_character_value_norm,
    main_old_signed_projected_character_value_norm]

/-- The actual projected real white kernel has norm independent of position. -/
theorem main_old_signed_projected_white_kernel_norm_eq
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) (i j : Fin 2) :
    ‖oldSignedProjectedWhiteKernel b L x i j‖ =
      ‖oldSignedProjectedWhiteKernel b L 0 i j‖ := by
  calc
    ‖oldSignedProjectedWhiteKernel b L x i j‖ =
        ‖oldSignedWhiteComplexify (oldSignedProjectedWhiteKernel b L x i j)‖ :=
      (main_old_signed_white_complexify_norm _).symm
    _ = ‖oldSignedSpectralWhiteInverse b L
          (oldSignedProjectedCharacter b x i j)‖ := by
      rw [old_signed_projected_white_kernel_complexify]
    _ = ‖oldSignedProjectedCharacter b x i j‖ :=
      (oldSignedSpectralWhiteInverse b L).norm_map _
    _ = ‖oldSignedProjectedCharacter b 0 i j‖ :=
      main_old_signed_projected_character_norm_eq b x 0 i j
    _ = ‖oldSignedSpectralWhiteInverse b L
          (oldSignedProjectedCharacter b 0 i j)‖ :=
      ((oldSignedSpectralWhiteInverse b L).norm_map _).symm
    _ = ‖oldSignedWhiteComplexify (oldSignedProjectedWhiteKernel b L 0 i j)‖ := by
      rw [old_signed_projected_white_kernel_complexify]
    _ = ‖oldSignedProjectedWhiteKernel b L 0 i j‖ :=
      main_old_signed_white_complexify_norm _

/-- A finite uniform bound for every rotated projected kernel value. -/
theorem main_old_signed_rotated_white_kernel_norm_le
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) (i j : Fin 2) :
    ‖oldSignedRotatedWhiteKernel b L x i j‖ ≤
      ∑ a : Fin 2, ∑ c : Fin 2,
        ‖oldSignedProjectedWhiteKernel b L 0 a c‖ := by
  unfold oldSignedRotatedWhiteKernel
  calc
    _ ≤ ∑ a : Fin 2, ‖∑ c : Fin 2,
        (responsePlanarJ i a * responsePlanarJ c j) •
          oldSignedProjectedWhiteKernel b L x a c‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin 2, ∑ c : Fin 2,
        ‖oldSignedProjectedWhiteKernel b L 0 a c‖ := by
      apply Finset.sum_le_sum
      intro a _
      calc
        ‖∑ c : Fin 2,
            (responsePlanarJ i a * responsePlanarJ c j) •
              oldSignedProjectedWhiteKernel b L x a c‖
            ≤ ∑ c : Fin 2,
              ‖(responsePlanarJ i a * responsePlanarJ c j) •
                oldSignedProjectedWhiteKernel b L x a c‖ := norm_sum_le _ _
        _ ≤ ∑ c : Fin 2, ‖oldSignedProjectedWhiteKernel b L 0 a c‖ := by
          apply Finset.sum_le_sum
          intro c _
          rw [norm_smul, Real.norm_eq_abs]
          have hJ₁ : |responsePlanarJ i a| ≤ 1 := by
            fin_cases i <;> fin_cases a <;> norm_num [responsePlanarJ]
          have hJ₂ : |responsePlanarJ c j| ≤ 1 := by
            fin_cases c <;> fin_cases j <;> norm_num [responsePlanarJ]
          calc
            |responsePlanarJ i a * responsePlanarJ c j| *
                ‖oldSignedProjectedWhiteKernel b L x a c‖
                ≤ 1 * ‖oldSignedProjectedWhiteKernel b L x a c‖ := by
                  rw [abs_mul]
                  calc
                    |responsePlanarJ i a| * |responsePlanarJ c j| *
                        ‖oldSignedProjectedWhiteKernel b L x a c‖
                        ≤ 1 * 1 * ‖oldSignedProjectedWhiteKernel b L x a c‖ := by
                          gcongr
                    _ = 1 * ‖oldSignedProjectedWhiteKernel b L x a c‖ := by ring
            _ = ‖oldSignedProjectedWhiteKernel b L x a c‖ := one_mul _
            _ = ‖oldSignedProjectedWhiteKernel b L 0 a c‖ :=
              main_old_signed_projected_white_kernel_norm_eq b L x a c

/-- The spectral q3 character map is continuous in physical position. Its
distance formula follows from the exact q3 covariance Gram kernel. -/
private theorem main_q3_spectral_character_distance_sq
    (b : ℝ) (x y : Vec 2) :
    ‖q3SpectralCharacter b (q3SpectralPoint y) -
      q3SpectralCharacter b (q3SpectralPoint x)‖ ^ 2 =
      2 * b ^ 2 - 2 * b ^ 2 *
        q3Cov (y 0 - x 0) * q3Cov (y 1 - x 1) := by
  rw [norm_sub_sq (𝕜 := ℂ), q3SpectralCharacter_norm_sq,
    q3SpectralCharacter_norm_sq, q3SpectralCharacter_inner]
  simp [q3SpectralPoint]
  rw [show x 0 - y 0 = -(y 0 - x 0) by ring,
    show x 1 - y 1 = -(y 1 - x 1) by ring,
    q3Cov_even, q3Cov_even]
  rw [← Complex.ofReal_pow]
  simp only [Complex.ofReal_re]
  ring

/-- Exact spectral q3 characters vary continuously in L² with the spatial
point, by their covariance formula and continuity of `q3Cov`. -/
theorem main_q3_spectral_character_continuous (b : ℝ) :
    Continuous (fun x : Vec 2 => q3SpectralCharacter b (q3SpectralPoint x)) := by
  refine Metric.continuous_iff.mpr fun x ε hε => ?_
  let F : Vec 2 → ℝ := fun y =>
    ‖q3SpectralCharacter b (q3SpectralPoint y) -
      q3SpectralCharacter b (q3SpectralPoint x)‖ ^ 2
  have hFform (y : Vec 2) : F y =
      2 * b ^ 2 - 2 * b ^ 2 * q3Cov (y 0 - x 0) * q3Cov (y 1 - x 1) :=
    main_q3_spectral_character_distance_sq b x y
  have hq : Continuous q3Cov := ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hF : Continuous F := by
    have heq : F = fun y =>
        2 * b ^ 2 - 2 * b ^ 2 * q3Cov (y 0 - x 0) * q3Cov (y 1 - x 1) :=
      funext hFform
    rw [heq]
    fun_prop
  have hFx : F x = 0 := by
    rw [hFform]
    simp [q3Cov_zero_eq_one]
  obtain ⟨δ, hδ, hδbound⟩ :=
    (Metric.continuous_iff.mp hF) x (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hsmall := hδbound y hy
  have hFy : 0 ≤ F y := by
    dsimp [F]
    positivity
  have hFlt : F y < ε ^ 2 := by
    change ‖F y - F x‖ < ε ^ 2 at hsmall
    rw [hFx, sub_zero, Real.norm_eq_abs, abs_of_nonneg hFy] at hsmall
    exact hsmall
  have hnorm : ‖q3SpectralCharacter b (q3SpectralPoint y) -
      q3SpectralCharacter b (q3SpectralPoint x)‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp (by simpa [F] using hFlt)
  simpa [dist_eq_norm] using hnorm

/-- Multiplication by the OLD Helmholtz entry contracts the spectral L²
distance, so the projected spectral characters are also continuous. -/
theorem main_old_signed_projected_character_dist_le
    (b : ℝ) (x y : Vec 2) (i j : Fin 2) :
    dist (oldSignedProjectedCharacter b x i j)
      (oldSignedProjectedCharacter b y i j) ≤
    dist (q3SpectralCharacter b (q3SpectralPoint x))
      (q3SpectralCharacter b (q3SpectralPoint y)) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (oldSignedProjectedCharacter b x i j)
      (oldSignedProjectedCharacter b y i j),
    Lp.coeFn_sub (q3SpectralCharacter b (q3SpectralPoint x))
      (q3SpectralCharacter b (q3SpectralPoint y)),
    old_signed_projected_character_coeFn b x i j,
    old_signed_projected_character_coeFn b y i j,
    q3SpectralCharacter_coeFn b (q3SpectralPoint x),
    q3SpectralCharacter_coeFn b (q3SpectralPoint y)] with ξ hps hcs hpx hpy hcx hcy
  change (oldSignedProjectedCharacter b x i j -
      oldSignedProjectedCharacter b y i j) ξ =
    oldSignedProjectedCharacter b x i j ξ - oldSignedProjectedCharacter b y i j ξ at hps
  change (q3SpectralCharacter b (q3SpectralPoint x) -
      q3SpectralCharacter b (q3SpectralPoint y)) ξ =
    q3SpectralCharacter b (q3SpectralPoint x) ξ -
      q3SpectralCharacter b (q3SpectralPoint y) ξ at hcs
  change oldSignedProjectedCharacter b x i j ξ = _ at hpx
  change oldSignedProjectedCharacter b y i j ξ = _ at hpy
  change q3SpectralCharacter b (q3SpectralPoint x) ξ = _ at hcx
  change q3SpectralCharacter b (q3SpectralPoint y) ξ = _ at hcy
  rw [hps, hcs, hpx, hpy, hcx, hcy]
  simp only [oldSignedProjectedCharacterValue, q3SpectralPoint,
    WithLp.toLp_fst, WithLp.toLp_snd]
  rw [← mul_sub, Complex.norm_mul]
  have hh : ‖(oldSignedHelmholtzEntry ξ i j : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact old_signed_helmholtz_entry_abs ξ i j
  calc
    ‖(oldSignedHelmholtzEntry ξ i j : ℂ)‖ *
        ‖exp (((2 * Real.pi * (ξ.fst * x 0 + ξ.snd * x 1) : ℝ) : ℂ) * I) -
          exp (((2 * Real.pi * (ξ.fst * y 0 + ξ.snd * y 1) : ℝ) : ℂ) * I)‖
        ≤ 1 * _ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ = _ := one_mul _

/-- The projected spectral characters vary continuously in the spatial
point. -/
theorem main_old_signed_projected_character_continuous
    (b : ℝ) (i j : Fin 2) :
    Continuous (fun x : Vec 2 => oldSignedProjectedCharacter b x i j) := by
  refine Metric.continuous_iff.mpr fun x ε hε => ?_
  obtain ⟨δ, hδ, hchar⟩ :=
    (Metric.continuous_iff.mp (main_q3_spectral_character_continuous b)) x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  exact (main_old_signed_projected_character_dist_le b y x i j).trans_lt (hchar y hy)

/-- The actual OLD projected real white kernel is continuous in its spatial
point, since it is the image of the projected spectral character under the
fixed spectral isometry and real-part map. -/
theorem main_old_signed_projected_white_kernel_continuous
    (b : ℝ) (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    Continuous (fun x : Vec 2 => oldSignedProjectedWhiteKernel b L x i j) := by
  have hp := main_old_signed_projected_character_continuous b i j
  have hi := (oldSignedSpectralWhiteInverse b L).continuous.comp hp
  exact oldSignedWhiteRealPart.continuous.comp hi

end ASDExplicitGamma.Main
