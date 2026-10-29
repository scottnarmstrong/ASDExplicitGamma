module

public import ASDExplicitGamma.Numerics.Inverse.MomentsInverse

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invFirstEd : ℚ := invE ((17444/10000)*(1+invInverseTau)*(10/(16000000*(1+invInverseTau))))

def invFirstC : ℚ := 3*(2700*3^80+1)

def invFirstM0 : ℚ := (2/3)*(1/3^336)/(66/100)^2

def invFirstZ0 : ℚ := (1/3^166)/(41/100)^2

def invFirstLi : ℚ := invFirstEd*((29 / 25 : ℚ)+invFirstC*(12*invInverseTau+2)*invInverseM2)*invLayer (2*invGamma)

def invFirstRho : ℚ := invFirstEd*(4096*(2*invInverseTau+2)*invFirstM0+3*invFirstC*(12*invInverseTau+2)*invFirstZ0)+2/10^40

def invFirstA : ℚ := invE (11/5*invGamma)*invE (11*invGamma)*invFirstLi*invE (11/5*invGamma*350)*invSB

def invFirste : ℚ := invE (11/5*invGamma)*(509/500)*invE (11*invGamma)*invPopulationRoot*invFirstRho*invSR

theorem invFirst_outputs :
    invFirstA+invFirste < (159 / 100 : ℚ) ∧ invFirstA+1/2000 < (159 / 100 : ℚ) ∧ invFirste^2/(4*(1/2000)) < (3 / 10000000000000000000000000000000000000000000000 : ℚ) := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
