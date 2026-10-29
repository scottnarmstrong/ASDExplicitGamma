module

public import ASDExplicitGamma.Numerics.Inverse.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invLayerRoot : ℚ := (5773502691896257645091487805019574556476017512701268760186023264839776723029333456937153955857495253 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invLayerRoot_bracket :
    0 < invLayerRoot ∧ (1/3 : ℚ) < invLayerRoot^2 := by
  decide +kernel

def invT (a z : ℚ) : ℚ := (a*z^2+a^2*z^3+a^3*z^4)/(1-a^3*z^4)

def invTf (a z : ℚ) : ℚ := (2*a*z^2+3*a^2*z^3+4*a^3*z^4)/(1-a^3*z^4)+4*a^3*z^4*(a*z^2+a^2*z^3+a^3*z^4)/(1-a^3*z^4)^2

theorem invLayer_exact_at_zero :
    8*invT (1/3) 1-32*invT (1/9) 1+1 = 1 ∧ 8*invTf (1/3) 1-32*invTf (1/9) 1+2 = 332/91 := by
  decide +kernel

def invExactLayerTwo : ℚ := 8*invT (1/3) (invE (11/10*2*invGamma))-32*invT (1/9) (invE (11/10*2*invGamma))+(invE (11/10*2*invGamma))^2

theorem invLayer_majorant_Two :
    invExactLayerTwo < invLayer (2*invGamma) := by
  decide +kernel

def invExactLayerFour : ℚ := 8*invT (1/3) (invE (11/10*4*invGamma))-32*invT (1/9) (invE (11/10*4*invGamma))+(invE (11/10*4*invGamma))^2

theorem invLayer_majorant_Four :
    invExactLayerFour < invLayer (4*invGamma) := by
  decide +kernel

theorem invLayerF_majorant :
    8*invTf (1/3) (invE (11/10*4*invGamma))-32*invTf (1/9) (invE (11/10*4*invGamma))+2*(invE (11/10*4*invGamma))^2 < invLayerF (4*invGamma) := by
  decide +kernel

def invLayerZ : ℚ := invE (22/5*invGamma)

def invL0 : ℚ := 2*invT invLayerRoot invLayerZ

def invL1 : ℚ := 2*invTf invLayerRoot invLayerZ

def invL0plus : ℚ := invLayerZ^2/3+(2829/1000)*(invT invLayerRoot invLayerZ-invLayerRoot*invLayerZ^2)

def invL1plus : ℚ := 2*invLayerZ^2/3+(2829/1000)*(invTf invLayerRoot invLayerZ-2*invLayerRoot*invLayerZ^2)

theorem invLayer_positive_caps :
    invL0plus < 2.581530 ∧ invL1plus < 11.427529 ∧ invL0plus < invL0 ∧ invL1plus-invL1 < 350*(invL0-invL0plus) := by
  decide +kernel

theorem invLayer_domains :
    0 < 1-(1/3 : ℚ)^3*(invE (11/10*4*invGamma))^4 ∧ 0 < 1-invLayerRoot^3*invLayerZ^4 ∧ (8 : ℚ) < (2829/1000)^2 ∧ invL0 < 3 ∧ invL1 < 15 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
