module

public import ASDExplicitGamma.Native.OldSignedProjectedDerivativeData

/-! Strong spatial derivatives of the actual projected characters, with
all frequency growth paid by a proved spectral L2 envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- The projected character has its actual first-frequency strong L2
derivative, rather than only a formal pointwise Fourier derivative. -/
theorem old_signed_projected_character_hasFDerivAt (b : ℝ) (x : Vec 2) (i j : Fin 2) :
    HasFDerivAt (fun y => oldSignedProjectedCharacter b y i j)
      (oldSignedProjectedSpatialDerivative b x i j) x := by
  apply old_signed_hasFDerivAt_L2 (q3SpectralMeasure b)
    (fun y => oldSignedProjectedCharacter b y i j) (fun y => oldSignedProjectedCharacterValue y i j) x
    (oldSignedProjectedSpatialDerivative b x i j) (oldSignedProjectedPointDerivative x i j)
    (oldSignedFrequencyEnvelope b) (fun y => old_signed_projected_character_coeFn b y i j)
    (fun v => old_signed_projected_spatial_derivative_coeFn b x v i j)
    (Filter.Eventually.of_forall (old_signed_projected_point_hasFDerivAt x i j))
  intro y
  filter_upwards [old_signed_frequency_envelope_coeFn b] with xi hb
  have hz : 0≤4*Real.pi*(|oldSignedFrequency xi 0| + |oldSignedFrequency xi 1|) := by positivity
  rw [hb,Real.norm_of_nonneg hz]
  have hi := old_signed_projected_character_increment_norm x y i j xi
  have hd := old_signed_projected_point_derivative_norm x (y-x) i j xi
  calc
    _ ≤ ‖oldSignedProjectedCharacterValue y i j xi-oldSignedProjectedCharacterValue x i j xi‖+
        ‖oldSignedProjectedPointDerivative x i j xi (y-x)‖ := norm_sub_le _ _
    _ ≤ 2*Real.pi*(|xi.fst| + |xi.snd|)*‖y-x‖+
        2*Real.pi*(|xi.fst| + |xi.snd|)*‖y-x‖ := add_le_add hi hd
    _ = _ := by
      norm_num [oldSignedFrequency]
      ring

/-- Each first-frequency derivative multiplier is strongly continuous.
Its L2 frequency majorant is independent of the spatial point. -/
theorem old_signed_projected_derivative_continuous (b : ℝ) (i j k : Fin 2) :
    Continuous (fun x : Vec 2 => oldSignedProjectedDerivative b x i j k) := by
  let B : Lp ℝ 2 (q3SpectralMeasure b) :=
    (((old_signed_frequency_memLp b k).norm).const_mul (2*Real.pi)).toLp _
  apply old_signed_continuous_L2 (q3SpectralMeasure b)
    (fun x => oldSignedProjectedDerivative b x i j k)
    (fun x => oldSignedProjectedDerivativeValue x i j k) B
    (fun x => old_signed_projected_derivative_coeFn b x i j k)
  · apply Filter.Eventually.of_forall
    intro xi
    unfold oldSignedProjectedDerivativeValue oldSignedProjectedCharacterValue
    fun_prop
  · intro x
    have hB : (B : Q3FrequencyPlane → ℝ) =ᵐ[q3SpectralMeasure b]
        fun xi => 2*Real.pi*‖oldSignedFrequency xi k‖ :=
      (((old_signed_frequency_memLp b k).norm).const_mul (2*Real.pi)).coeFn_toLp
    filter_upwards [hB] with xi hB
    rw [hB,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi*‖oldSignedFrequency xi k‖)]
    simpa only [Real.norm_eq_abs] using old_signed_projected_derivative_value_norm x i j k xi

/-- The complete projected field is C1 as a spectral L2 family. -/
theorem old_signed_projected_character_contDiff (b : ℝ) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x : Vec 2 => oldSignedProjectedCharacter b x i j) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨(fun x => oldSignedProjectedSpatialDerivative b x i j),?_,fun x => old_signed_projected_character_hasFDerivAt b x i j⟩
  have h0 := (ContinuousLinearMap.smulRightL ℝ (Vec 2) (Lp ℂ 2 (q3SpectralMeasure b))
    (ContinuousLinearMap.proj 0)).continuous.comp (old_signed_projected_derivative_continuous b i j 0)
  have h1 := (ContinuousLinearMap.smulRightL ℝ (Vec 2) (Lp ℂ 2 (q3SpectralMeasure b))
    (ContinuousLinearMap.proj 1)).continuous.comp (old_signed_projected_derivative_continuous b i j 1)
  exact h0.add h1

end
end ASDExplicitGamma.Native
