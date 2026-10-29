module

public import ASDExplicitGamma.Native.HeatOldStepSound

/-! The real four-pass source profile is below the literal OLD producer. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- Finite OLD refinement soundness, using only its checked radical inputs. -/
theorem heat_old_iteration_sound (height : ℕ) (f e hc : ℚ) (steps : ℕ)
    (hf : 0 ≤ f) (he : 0 ≤ e)
    (hraw : nativeSourceRawMomentIncrement height e f ≤ (hc:ℝ))
    (hcheck : ∀ n < steps,HeatOldStepValid f (heatOldIncrement height f e hc n)) :
    nativeSourceGenericPassCap height nativeA e f steps ≤
      (heatOldIncrement height f e hc steps:ℝ) := by
  have hbound : ∀ n,n ≤ steps → nativeSourceGenericPassCap height nativeA e f n ≤
      (heatOldIncrement height f e hc n:ℝ) := by
    intro n
    induction n with
    | zero => intro _; exact hraw
    | succ n ih =>
      intro hn
      have hcap := native_source_generic_individual_nonneg height (nativeA:ℝ) e f
        (by norm_num [nativeA]) (by exact_mod_cast he) (by exact_mod_cast hf) n
      exact heat_old_step_sound height f e (heatOldIncrement height f e hc n) hf he
        (hcheck n (by omega)) (nativeSourceGenericPassCap height nativeA e f n)
        hcap (ih (by omega))
  exact hbound steps le_rfl

/-- After four refinements, the outward-rounded OLD x slot controls the
entire real initial-plus-increment source profile. -/
theorem heat_old_four_profile_sound (height : ℕ) (f e hc : ℚ)
    (hf : 0 ≤ f) (he : 0 ≤ e)
    (hraw : nativeSourceRawMomentIncrement height e f ≤ (hc:ℝ))
    (hcheck : ∀ n < 4,HeatOldStepValid f (heatOldIncrement height f e hc n)) :
    nativeSourceGenericIndividualCap height nativeA e f 4 ≤
      ((nativeOldFrom height f e hc).x:ℝ) := by
  rw [heat_old_from_four]
  have h := heat_old_iteration_sound height f e hc 4 hf he hraw hcheck
  have hsum := add_le_add (le_refl ((7/2)*(nativeA:ℝ))) h
  have hround : (((7/2)*nativeA+heatOldIncrement height f e hc 4:ℚ):ℝ) ≤
      (nativeUp ((7/2)*nativeA+heatOldIncrement height f e hc 4):ℝ) := by
    exact_mod_cast nativeUp_ge ((7/2)*nativeA+heatOldIncrement height f e hc 4)
  apply le_trans ?_ hround
  simpa only [nativeSourceGenericIndividualCap,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hsum

end
end ASDExplicitGamma.Native
