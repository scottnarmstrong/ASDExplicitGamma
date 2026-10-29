module

public import ASDExplicitGamma.Native.OldSignedCovariance
public import ASDExplicitGamma.Native.OldSignedSpectralReality

/-! The bounded whole-plane Helmholtz multiplier applied to the physical
q3 kernel characters. Every filtered character is genuine spectral L2. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

private theorem old_signed_square_ratio_abs (x y : ℝ) :
    |x^2/(x^2+y^2)| ≤ 1 := by
  by_cases hz : x^2+y^2=0
  · rw [hz,div_zero,abs_zero]; norm_num
  have hd : 0<x^2+y^2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hz)
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le)]
  exact (div_le_one hd).mpr (le_add_of_nonneg_right (sq_nonneg _))

private theorem old_signed_cross_ratio_abs (x y : ℝ) :
    |x*y/(x^2+y^2)| ≤ 1 := by
  by_cases hz : x^2+y^2=0
  · rw [hz,div_zero,abs_zero]; norm_num
  have hd : 0<x^2+y^2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hz)
  rw [abs_div,abs_of_pos hd]
  apply (div_le_one hd).mpr
  rw [abs_mul]
  nlinarith only [sq_nonneg (|x|-|y|),sq_abs x,sq_abs y,sq_nonneg x,sq_nonneg y]

/-- Every entry of the Helmholtz multiplier is bounded, including at zero. -/
theorem old_signed_helmholtz_entry_abs (xi : Q3FrequencyPlane) (i j : Fin 2) :
    |oldSignedHelmholtzEntry xi i j| ≤ 1 := by
  fin_cases i <;> fin_cases j
  · simpa [oldSignedHelmholtzEntry,oldSignedFrequency,pow_two] using old_signed_square_ratio_abs xi.fst xi.snd
  · simpa [oldSignedHelmholtzEntry,oldSignedFrequency] using old_signed_cross_ratio_abs xi.fst xi.snd
  · simpa [oldSignedHelmholtzEntry,oldSignedFrequency,mul_comm] using old_signed_cross_ratio_abs xi.fst xi.snd
  · simpa [oldSignedHelmholtzEntry,oldSignedFrequency,pow_two,add_comm] using old_signed_square_ratio_abs xi.snd xi.fst

/-- Frequency reflection leaves the real Helmholtz multiplier unchanged. -/
theorem old_signed_helmholtz_entry_neg (xi : Q3FrequencyPlane) (i j : Fin 2) :
    oldSignedHelmholtzEntry (-xi) i j=oldSignedHelmholtzEntry xi i j := by
  have hc (k : Fin 2) : oldSignedFrequency (-xi) k = -oldSignedFrequency xi k := by
    fin_cases k <;> simp [oldSignedFrequency]
  simp only [oldSignedHelmholtzEntry,hc,WithLp.neg_fst,WithLp.neg_snd,neg_mul_neg,neg_sq]

/-- The pointwise filtered spatial character, with no regularity assumption
at frequency zero and no replacement by a truncated multiplier. -/
def oldSignedProjectedCharacterValue (x : Vec 2) (i j : Fin 2) (xi : Q3FrequencyPlane) : ℂ :=
  (oldSignedHelmholtzEntry xi i j:ℂ)*
    exp ((((2*Real.pi*(xi.fst*x 0+xi.snd*x 1)):ℝ):ℂ)*I)

/-- The full filtered character is square integrable for the actual finite
spectral measure. -/
theorem old_signed_projected_character_memLp (b : ℝ) (x : Vec 2) (i j : Fin 2) :
    MemLp (oldSignedProjectedCharacterValue x i j) 2 (q3SpectralMeasure b) := by
  apply MemLp.of_bound (C := 1)
  · apply Measurable.aestronglyMeasurable
    have hc (k : Fin 2) : Measurable (fun xi : Q3FrequencyPlane => oldSignedFrequency xi k) := by
      unfold oldSignedFrequency
      split_ifs <;> fun_prop
    have he : Measurable (fun xi => oldSignedHelmholtzEntry xi i j) :=
      ((hc i).mul (hc j)).div (by fun_prop)
    exact he.complex_ofReal.mul (by fun_prop)
  · filter_upwards [] with xi
    rw [oldSignedProjectedCharacterValue,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
      Complex.norm_real,Real.norm_eq_abs]
    exact old_signed_helmholtz_entry_abs xi i j

/-- The actual spectral L2 element for one projected physical load component. -/
def oldSignedProjectedCharacter (b : ℝ) (x : Vec 2) (i j : Fin 2) : Lp ℂ 2 (q3SpectralMeasure b) :=
  (old_signed_projected_character_memLp b x i j).toLp _

/-- The L2 element has the full untruncated source formula. -/
theorem old_signed_projected_character_coeFn (b : ℝ) (x : Vec 2) (i j : Fin 2) :
    (oldSignedProjectedCharacter b x i j : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      oldSignedProjectedCharacterValue x i j :=
  (old_signed_projected_character_memLp b x i j).coeFn_toLp

/-- The filtered character is fixed by spectral reality, so its physical
white-noise image will be real rather than merely complex. -/
theorem old_signed_projected_character_real (b : ℝ) (x : Vec 2) (i j : Fin 2) :
    oldSignedSpectralReality b (oldSignedProjectedCharacter b x i j) =
      oldSignedProjectedCharacter b x i j := by
  apply Lp.ext
  have he := old_signed_projected_character_coeFn b x i j
  have hn := (old_signed_spectral_neg_measurePreserving b).quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [old_signed_spectral_reality_coeFn b _,he,hn] with xi hr hx hn
  dsimp only [Function.comp_def] at hn
  rw [hr,hn,hx]
  dsimp only [oldSignedProjectedCharacterValue]
  rw [map_mul,Complex.conj_ofReal,old_signed_helmholtz_entry_neg,←Complex.exp_conj]
  congr 2
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,WithLp.neg_fst,WithLp.neg_snd]
  push_cast
  ring

end
end ASDExplicitGamma.Native
