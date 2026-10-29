module

public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.RadicalProfile

/-! Literal affine-radical expansion of the full main error formula. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

/-- The constant under the inverse source-square root. -/
def mainErrorSourceRoot (H xi : ℝ) : ℝ :=
  Real.sqrt (mainBeta*xi+mainEpsNew*mainD*mainBeta*H)

/-- Coefficients of the three remaining radicals after expanding the squares. -/
def mainErrorWeights (v H xi ecov be kd krem op om : ℝ) : Fin 3 → ℝ :=
  ![2*krem*mainT0 xi*Real.sqrt v + Real.sqrt 2*mainT0 xi*ecov +
      2*mainKa v*mainLoadQ H op om + 2*kd*(63/50)*Real.sqrt 2*mainBeta*mainKa v,
    2*mainKa v*kd*mainErrorSourceRoot H xi + 2*kd*(63/50)*mainKa v*mainRec xi,
    2*be]

def mainErrorOffsets (a H xi : ℝ) : Fin 3 → ℝ :=
  ![mainBeta*a+mainEpsNew*mainHd H,
    mainBeta^2*a+(2*mainBeta*mainEpsNew+mainEpsNew^2)*mainHd H, xi]

def mainErrorRates : Fin 3 → ℝ := ![mainBeta, mainBeta^2, mainBetaOld]

def mainErrorSlope (v : ℝ) : ℝ := v/2*mainBeta+(mainKa v)^2*mainBeta^2

end
end ASDExplicitGamma.Main
