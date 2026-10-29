module

public import ASDExplicitGamma.Numerics.Inverse.MomentsInverse

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invLocalEd : ℚ := invE ((17444/10000)*(1+invInverseTau)*(10/(16000000*(1+invInverseTau))))

def invLocalC : ℚ := 3*(2700*3^80+1)

def invLocalM0 : ℚ := (2/3)*(1/3^336)/(66/100)^2

def invLocalZ0 : ℚ := (1/3^166)/(41/100)^2

def invLocalLi : ℚ := invLocalEd*((10747 / 10000 : ℚ)+invLocalC*(12*invInverseTau+2)*invInverseM2)*invLayer (2*invGamma)

def invLocalRho : ℚ := invLocalEd*(4096*(2*invInverseTau+2)*invLocalM0+3*invLocalC*(12*invInverseTau+2)*invLocalZ0)+2/10^40

def invLocalA : ℚ := invE (11/5*invGamma)*invE (11*invGamma)*invLocalLi*invE (11/5*invGamma*350)*invSB

def invLocale : ℚ := invE (11/5*invGamma)*(509/500)*invE (11*invGamma)*invPopulationRoot*invLocalRho*invSR

theorem invLocal_outputs :
    invLocalA+invLocale < (3683 / 2500 : ℚ) ∧ invLocalA+1/2000 < (3683 / 2500 : ℚ) ∧ invLocale^2/(4*(1/2000)) < (3 / 10000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
