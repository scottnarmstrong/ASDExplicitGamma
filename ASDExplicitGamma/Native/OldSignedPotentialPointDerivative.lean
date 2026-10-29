module

public import ASDExplicitGamma.Native.OldSignedPotentialIncrement
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The exact pointwise derivative of the inverse-gradient potential
is the Helmholtz-projected character, before passage to strong L2. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- The Fourier phase as an actual continuous real-linear functional. -/
def oldSignedPhaseDerivative (xi : Q3FrequencyPlane) : Vec 2 →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj 0).smulRight (((2*Real.pi*xi.fst:ℝ):ℂ)*I)+
    (ContinuousLinearMap.proj 1).smulRight (((2*Real.pi*xi.snd:ℝ):ℂ)*I)

/-- Evaluation of the phase derivative is the original Fourier phase. -/
theorem old_signed_phase_derivative_apply (xi : Q3FrequencyPlane) (v : Vec 2) :
    oldSignedPhaseDerivative xi v=oldSignedPotentialPhase v xi := by
  change (v 0:ℝ) • (((2*Real.pi*xi.fst:ℝ):ℂ)*I)+
    (v 1:ℝ) • (((2*Real.pi*xi.snd:ℝ):ℂ)*I)=_
  simp only [oldSignedPotentialPhase,Complex.real_smul]
  push_cast
  ring

/-- The two components of the physical projected gradient, as a real-linear
functional of the spatial increment. -/
def oldSignedPotentialPointDerivative (x : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) :
    Vec 2 →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj 0).smulRight (oldSignedProjectedCharacterValue x 0 j xi)+
    (ContinuousLinearMap.proj 1).smulRight (oldSignedProjectedCharacterValue x 1 j xi)

/-- The potential is differentiable even at frequency zero (where its
canonical derivative is also zero). -/
theorem old_signed_potential_point_hasFDerivAt (x : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) :
    HasFDerivAt (fun y => oldSignedPotentialValue y j xi)
      (oldSignedPotentialPointDerivative x j xi) x := by
  have hphase : HasFDerivAt (fun y => oldSignedPotentialPhase y xi) (oldSignedPhaseDerivative xi) x := by
    have he : (fun y => oldSignedPotentialPhase y xi)=oldSignedPhaseDerivative xi :=
      funext (fun y => (old_signed_phase_derivative_apply xi y).symm)
    rw [he]
    exact (oldSignedPhaseDerivative xi).hasFDerivAt
  let c : ℂ := (oldSignedFrequency xi j:ℂ)/(((2*Real.pi*(xi.fst^2+xi.snd^2):ℝ):ℂ)*I)
  have hh := (hphase.cexp.sub_const 1).const_mul c
  change HasFDerivAt (fun y => oldSignedPotentialValue y j xi)
    (c • (exp (oldSignedPotentialPhase x xi) • oldSignedPhaseDerivative xi)) x at hh
  convert hh using 1
  ext v
  by_cases hz : xi.fst^2+xi.snd^2=0
  · simp [oldSignedPotentialPointDerivative,oldSignedProjectedCharacterValue,
      oldSignedHelmholtzEntry,hz,c]
  have hc : (((xi.fst^2+xi.snd^2:ℝ):ℂ))≠0 := Complex.ofReal_ne_zero.mpr hz
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  fin_cases j
  all_goals
    norm_num [oldSignedPotentialPointDerivative,oldSignedPhaseDerivative,
    oldSignedProjectedCharacterValue,oldSignedHelmholtzEntry,oldSignedFrequency,
    oldSignedPotentialPhase,c]
    field_simp [hc,hpi,Complex.I_ne_zero]

/-- The derivative is uniformly bounded in frequency by the l1 norm of its
spatial argument; no inverse frequency remains. -/
theorem old_signed_potential_point_derivative_norm (x v : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedPotentialPointDerivative x j xi v‖ ≤ |v 0| + |v 1| := by
  have hk (k : Fin 2) : ‖oldSignedProjectedCharacterValue x k j xi‖≤1 := by
    rw [oldSignedProjectedCharacterValue,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
      Complex.norm_real,Real.norm_eq_abs]
    exact old_signed_helmholtz_entry_abs xi k j
  change ‖(v 0:ℝ) • oldSignedProjectedCharacterValue x 0 j xi+
    (v 1:ℝ) • oldSignedProjectedCharacterValue x 1 j xi‖ ≤ _
  calc
    _ ≤ ‖(v 0:ℝ) • oldSignedProjectedCharacterValue x 0 j xi‖+
        ‖(v 1:ℝ) • oldSignedProjectedCharacterValue x 1 j xi‖ := norm_add_le _ _
    _ ≤ |v 0| * 1+|v 1| * 1 := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (hk 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hk 1) (abs_nonneg _))
    _ = _ := by ring

end
end ASDExplicitGamma.Native
