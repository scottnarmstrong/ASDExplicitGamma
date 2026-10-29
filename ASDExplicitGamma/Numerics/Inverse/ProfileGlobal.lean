module

public import ASDExplicitGamma.Numerics.Inverse.MomentsInverse

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invGlobalEd : ℚ := invE ((17444/10000)*(1+invInverseTau)*(10/(16000000*(1+invInverseTau))))

def invGlobalC : ℚ := 3*(2700*3^80+1)

def invGlobalM0 : ℚ := (2/3)*(1/3^293)/(66/100)^2

def invGlobalZ0 : ℚ := (1/3^145)/(41/100)^2

def invGlobalLi : ℚ := invGlobalEd*((10747 / 10000 : ℚ)+invGlobalC*(12*invInverseTau+2)*invInverseM2)*invLayer (2*invGamma)

def invGlobalRho : ℚ := invGlobalEd*(4096*(2*invInverseTau+2)*invGlobalM0+3*invGlobalC*(12*invInverseTau+2)*invGlobalZ0)+2/10^30

def invGlobalA : ℚ := invE (11/5*invGamma)*invE (11*invGamma)*invGlobalLi*invE (11/5*invGamma*306)*invSB

def invGlobale : ℚ := invE (11/5*invGamma)*(509/500)*invE (11*invGamma)*invPopulationRoot*invGlobalRho*invSR

theorem invGlobal_outputs :
    invGlobalA+invGlobale < (14103 / 10000 : ℚ) ∧ invGlobalA+1/2000 < (14103 / 10000 : ℚ) ∧ invGlobale^2/(4*(1/2000)) < (1 / 1000000000000000000000000 : ℚ) := by
  decide +kernel

theorem invGlobal_grouped :
    invGlobalA+1/2000+5/10^24 < (14103 / 10000 : ℚ) := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
