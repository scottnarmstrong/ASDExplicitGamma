module

public import ASDExplicitGamma.Native.OldSignedPotentialL2

/-! Frequency-uniform increments of the local projected potential. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- The source Fourier phase at a physical point measured in shell units. -/
def oldSignedPotentialPhase (x : Vec 2) (xi : Q3FrequencyPlane) : ℂ :=
  (((2*Real.pi*(xi.fst*x 0+xi.snd*x 1)):ℝ):ℂ)*I

/-- A difference of potential values equals a modulated potential difference.
The low-frequency cancellation is kept before taking any norm. -/
theorem old_signed_potential_increment (x y : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) :
    oldSignedPotentialValue y j xi-oldSignedPotentialValue x j xi =
      exp (oldSignedPotentialPhase x xi)*oldSignedPotentialValue (y-x) j xi := by
  have hp : oldSignedPotentialPhase x xi+oldSignedPotentialPhase (y-x) xi=
      oldSignedPotentialPhase y xi := by
    dsimp [oldSignedPotentialPhase]
    push_cast
    ring
  have he : exp (oldSignedPotentialPhase x xi)*exp (oldSignedPotentialPhase (y-x) xi)=
      exp (oldSignedPotentialPhase y xi) := by rw [←exp_add,hp]
  change _-_= exp (oldSignedPotentialPhase x xi)*
    ((oldSignedFrequency xi j:ℂ)/(((2*Real.pi*(xi.fst^2+xi.snd^2):ℝ):ℂ)*I)*
      (exp (oldSignedPotentialPhase (y-x) xi)-1))
  dsimp only [oldSignedPotentialValue]
  change _*(exp (oldSignedPotentialPhase y xi)-1)-
    _*(exp (oldSignedPotentialPhase x xi)-1)=_
  rw [←he]
  ring

/-- The potential increments are uniformly Lipschitz in the two spatial
coordinates, including all frequencies arbitrarily near zero. -/
theorem old_signed_potential_increment_norm (x y : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedPotentialValue y j xi-oldSignedPotentialValue x j xi‖ ≤
      |y 0-x 0|+|y 1-x 1| := by
  rw [old_signed_potential_increment,norm_mul]
  have hp : ‖exp (oldSignedPotentialPhase x xi)‖=1 := Complex.norm_exp_ofReal_mul_I _
  rw [hp,one_mul]
  exact old_signed_potential_value_norm (y-x) j xi

end
end ASDExplicitGamma.Native
