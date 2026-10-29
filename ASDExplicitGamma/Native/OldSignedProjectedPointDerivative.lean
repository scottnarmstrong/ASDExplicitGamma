module

public import ASDExplicitGamma.Native.OldSignedFrequencyL2

/-! Pointwise spatial derivatives and frequency-majorized increments of
the complete Helmholtz-projected characters. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- The Fourier phase has its actual first-frequency spatial bound. -/
theorem old_signed_phase_norm_bound (v : Vec 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedPotentialPhase v xi‖ ≤
      2*Real.pi*(|xi.fst| + |xi.snd|)*‖v‖ := by
  have hp : 0<2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hv (k : Fin 2) : |v k|≤‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v k
  rw [oldSignedPotentialPhase,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_mul,abs_of_pos hp]
  calc
    _ ≤ 2*Real.pi*(|xi.fst| * |v 0| + |xi.snd| * |v 1|) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])) hp.le
    _ ≤ 2*Real.pi*(|xi.fst| * ‖v‖+|xi.snd| * ‖v‖) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (hv 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hv 1) (abs_nonneg _))) hp.le
    _ = _ := by ring

/-- The purely imaginary phase has the exact unit-speed exponential bound. -/
theorem old_signed_phase_exp_sub_one_bound (v : Vec 2) (xi : Q3FrequencyPlane) :
    ‖exp (oldSignedPotentialPhase v xi)-1‖ ≤ ‖oldSignedPotentialPhase v xi‖ := by
  rw [oldSignedPotentialPhase,norm_mul,Complex.norm_I,mul_one,Complex.norm_real]
  simpa only [mul_comm _ I] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*(xi.fst*v 0+xi.snd*v 1)))

/-- Exact pointwise derivative of the complete filtered character. -/
def oldSignedProjectedPointDerivative (x : Vec 2) (i j : Fin 2) (xi : Q3FrequencyPlane) :
    Vec 2 →L[ℝ] ℂ :=
  oldSignedProjectedCharacterValue x i j xi • oldSignedPhaseDerivative xi

/-- Differentiating the complete projected character creates precisely its
first-frequency multiplier; the zero-frequency value remains canonical. -/
theorem old_signed_projected_point_hasFDerivAt (x : Vec 2) (i j : Fin 2) (xi : Q3FrequencyPlane) :
    HasFDerivAt (fun y => oldSignedProjectedCharacterValue y i j xi)
      (oldSignedProjectedPointDerivative x i j xi) x := by
  have he : (fun y => oldSignedPotentialPhase y xi)=oldSignedPhaseDerivative xi :=
    funext (fun y => (old_signed_phase_derivative_apply xi y).symm)
  have hd : HasFDerivAt (fun y => oldSignedPotentialPhase y xi) (oldSignedPhaseDerivative xi) x := by
    rw [he]
    exact (oldSignedPhaseDerivative xi).hasFDerivAt
  have hh := hd.cexp.const_mul (oldSignedHelmholtzEntry xi i j:ℂ)
  have heq : oldSignedProjectedPointDerivative x i j xi =
      (oldSignedHelmholtzEntry xi i j:ℂ) • (exp (oldSignedPotentialPhase x xi) • oldSignedPhaseDerivative xi) := by
    change ((oldSignedHelmholtzEntry xi i j:ℂ)*exp (oldSignedPotentialPhase x xi)) •
      oldSignedPhaseDerivative xi = _
    rw [mul_smul]
  change HasFDerivAt (fun y => oldSignedProjectedCharacterValue y i j xi)
    ((oldSignedHelmholtzEntry xi i j:ℂ) • (exp (oldSignedPotentialPhase x xi) • oldSignedPhaseDerivative xi)) x at hh
  rw [←heq] at hh
  exact hh

/-- The derivative's frequency bound is square integrable in the actual
spectral law; no higher-frequency supremum is introduced. -/
theorem old_signed_projected_point_derivative_norm (x v : Vec 2) (i j : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedProjectedPointDerivative x i j xi v‖ ≤
      2*Real.pi*(|xi.fst| + |xi.snd|)*‖v‖ := by
  change ‖oldSignedProjectedCharacterValue x i j xi*oldSignedPhaseDerivative xi v‖ ≤ _
  rw [norm_mul,old_signed_phase_derivative_apply]
  exact ((mul_le_mul_of_nonneg_right (old_signed_projected_character_value_norm x i j xi)
    (norm_nonneg _)).trans_eq (one_mul _)).trans (old_signed_phase_norm_bound v xi)

/-- Complete character increments have the same integrable frequency bound. -/
theorem old_signed_projected_character_increment_norm (x y : Vec 2) (i j : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedProjectedCharacterValue y i j xi-oldSignedProjectedCharacterValue x i j xi‖ ≤
      2*Real.pi*(|xi.fst| + |xi.snd|)*‖y-x‖ := by
  have hp : oldSignedPotentialPhase x xi+oldSignedPotentialPhase (y-x) xi=
      oldSignedPotentialPhase y xi := by
    dsimp [oldSignedPotentialPhase]
    push_cast
    ring
  have he : exp (oldSignedPotentialPhase x xi)*exp (oldSignedPotentialPhase (y-x) xi)=
      exp (oldSignedPotentialPhase y xi) := by rw [←exp_add,hp]
  have hf : oldSignedProjectedCharacterValue y i j xi-oldSignedProjectedCharacterValue x i j xi=
      (oldSignedHelmholtzEntry xi i j:ℂ)*exp (oldSignedPotentialPhase x xi)*
        (exp (oldSignedPotentialPhase (y-x) xi)-1) := by
    change _*exp (oldSignedPotentialPhase y xi)-_*exp (oldSignedPotentialPhase x xi)=_
    rw [←he]
    ring
  rw [hf,norm_mul,norm_mul,show ‖exp (oldSignedPotentialPhase x xi)‖=1 from
    Complex.norm_exp_ofReal_mul_I _,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact (((mul_le_mul_of_nonneg_right (old_signed_helmholtz_entry_abs xi i j)
    (norm_nonneg _)).trans_eq (one_mul _)).trans
    (old_signed_phase_exp_sub_one_bound (y-x) xi)).trans (old_signed_phase_norm_bound (y-x) xi)

end
end ASDExplicitGamma.Native
