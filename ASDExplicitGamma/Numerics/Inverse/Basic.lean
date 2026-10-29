module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Factorial.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invE (x : ℚ) : ℚ := 1 / (1-x)

def invLayer (t : ℚ) : ℚ := 1+4*(invE (11/5*t)/(3-invE (11/5*t))-1/2)

def invLayerF (t : ℚ) : ℚ := 332/91+8*(3*invE (11/5*t)/(3-invE (11/5*t))^2-3/4)

def invGamma : ℚ := 17/50000

def invAlphaUpper : ℚ := (7598356856515925473311877506545453353967734488873103186112886537003222331710472715944106141650371571 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invAlphaLower : ℚ := (7598356856515925473311877506545453353967734488873103186112886537003222331710472715944106141650271571 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invBetaUpper : ℚ := (8716855428717356829644793223500534615836898276249341990248370420588732802871618897021372933579825829 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invPopulationRoot : ℚ := (10641206399454099253731788764859183968604048834316040926397444871270868518952976641453063697888693687 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invHistoryRoot : ℚ := (7863750494990005865750738491395465436451567159067108171332141338736801674895182001718576575772036297 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invAlpha_bracket :
    0 < invAlphaLower ∧ invAlphaLower^4 < 1/3 ∧ (1/3 : ℚ) < invAlphaUpper^4 := by
  decide +kernel

theorem invBeta_bracket :
    0 < invBetaUpper ∧ invAlphaUpper < invBetaUpper^2 := by
  decide +kernel

theorem invPopulation_payment :
    invPopulationRoot^128 > (9^44 : ℚ) ∧ (509/500 : ℚ)^128 > 9 ∧ (5 : ℕ)^128 > 9^89 := by
  decide +kernel

theorem invHistoryRoot_bracket :
    0 < invHistoryRoot ∧ (1/3^7 : ℚ) < invHistoryRoot^32 := by
  decide +kernel

theorem invLayer_caps :
    invLayer (2*invGamma) < 1.004498093723 ∧ invLayer (4*invGamma) < 1.009016465899 ∧ invLayerF (4*invGamma) < 3.684458160277 := by
  decide +kernel

def invSB : ℚ := (1-invAlphaLower)/(1-invAlphaUpper*invE (11/5*invGamma))

def invSR : ℚ := (1-invAlphaLower)/(1-invBetaUpper*invE (11/5*invGamma))

theorem invHistory_denominators :
    0 < 1-invAlphaUpper*invE (11/5*invGamma) ∧ 0 < 1-invBetaUpper*invE (11/5*invGamma) ∧ invSR < 2 := by
  decide +kernel

def invSi : ℚ := (1-invAlphaLower)/(1-invHistoryRoot*invE (11/5*invGamma))

def invS0 : ℚ := (1-invAlphaLower)/(1-invHistoryRoot*invE (22/5*invGamma))

def invS1 : ℚ := (1-invAlphaLower)*(invHistoryRoot*invE (22/5*invGamma))/(1-invHistoryRoot*invE (22/5*invGamma))^2

theorem invFullHistory_caps :
    0 < 1-invHistoryRoot*invE (22/5*invGamma) ∧ invSi < 1.12734 ∧ invS0 < 1.130469 ∧ invS1 < 4.190715 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
