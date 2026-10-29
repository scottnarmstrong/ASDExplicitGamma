module

public import ASDExplicitGamma.Main.FlatFieldSpectralContraction
public import ASDExplicitGamma.Response.FrameAlgebra

/-! The signed whole-plane covariance contraction for the OLD trial.
The two quarter-turns are kept with their signs: J P J has mean -v I/2. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Response
noncomputable section

/-- Real planar coordinates of the q3 frequency variable. -/
def oldSignedFrequency (xi : Q3FrequencyPlane) : Vec 2 :=
  fun i => if i=0 then xi.fst else xi.snd

/-- An entry of the whole-plane gradient multiplier, with its canonical
zero value at frequency zero. The spectral measure has no atom there. -/
def oldSignedHelmholtzEntry (xi : Q3FrequencyPlane) (i j : Fin 2) : ℝ :=
  oldSignedFrequency xi i*oldSignedFrequency xi j/(xi.fst^2+xi.snd^2)

end
end ASDExplicitGamma.Native
