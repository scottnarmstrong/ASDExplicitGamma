module

public import ASDExplicitGamma.Numerics.Inverse.MomentsFull

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invFullEd : ℚ := invE ((17444/10000)*(1+invFullTau)*(10/(80*(1+invFullTau))))

def invFullC : ℚ := 3*(2700*3^80+1)

def invFullLi : ℚ := invFullEd*(1.16+invFullC*(12*invFullTau+2)*invFullM2)*invLayer (2*invGamma)

def invFullRho : ℚ := invFullEd*(4096*(2*invFullTau+2)*(2/3)*(1/3^336)/(66/100)^2+3*invFullC*(12*invFullTau+2)*(1/3^166)/(41/100)^2)+2/10^40

def invFullB0 : ℚ := invE (11*invGamma)*invFullLi*invE (11/5*invGamma*350)*invSB

def invFulle : ℚ := invE (11*invGamma)*invPopulationRoot*invFullRho*invSR

theorem invFull_positive_history :
    invFullB0+invFulle < 2.031006 ∧ invFulle^2/(4*(1/2000)) < 1/10^34 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
