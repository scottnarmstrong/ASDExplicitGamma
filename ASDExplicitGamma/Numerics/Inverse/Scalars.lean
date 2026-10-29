module

public import ASDExplicitGamma.Numerics.Inverse.ProfileFirst
public import ASDExplicitGamma.Numerics.Inverse.Full128

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invR40 : ℚ := invE (11/5*40*invGamma)

theorem invOnePass :
    invR40 = 6250/6063 ∧ invR40*(2+3/50+(711/40)*invGamma*(159/100)^3*invR40)-2 = 93698211491/627370137600 ∧ (93698211491/627370137600 : ℚ) < 747/5000 ∧ (711/40 : ℚ) = 2*(9/2)*(79/40) := by
  decide +kernel

theorem inv_band_exponents :
    (-19/2 : ℚ)+48*invGamma = -59273/6250 ∧ (-11/4 : ℚ)+48*invGamma = -34171/12500 ∧ (-7/2 : ℚ)+48*invGamma = -21773/6250 ∧ (-10 : ℚ)+48*invGamma = -31199/3125 := by
  decide +kernel

theorem inv_band_margin :
    (-19/2 : ℚ)+48*invGamma ≤ -5/2-2921/12500 ∧ (-11/4 : ℚ)+48*invGamma ≤ -5/2-2921/12500 ∧ (-7/2 : ℚ)+48*invGamma ≤ -5/2-2921/12500 ∧ (-10 : ℚ)+48*invGamma ≤ -5/2-2921/12500 ∧ (0 : ℚ) < 2921/12500 := by
  decide +kernel

def invTraceF : ℚ := 4*(2.018618+invGamma*(32474*(134+1)+11483216))*invE ((11/10)*(2*134+4)*invGamma)

def invTraceClock : ℚ := (9/2)*invGamma*invE ((11/10)*2*invGamma*134)

def invTraceC : ℚ := invTraceClock*(((4*20-2)*134+4*(20-1)*(521/1000))*1.4732+(2*(521/1000)*1.4732+(1975/1000+2*(20-1)*(1565/1000))*1.4732^2)*invTraceF)

def invTraceM : ℚ := invE ((11/10)*2*invGamma*134)*((1+1/1000)*(21/100+invTraceC)+8*(1+1000)*((11/10)*invGamma*134)^2)

theorem invTrace_coefficient :
    invTraceM = 7808009959887620355233361/1262543836738528000000 ∧ invTraceM < 10^6 ∧ 5400*(1/10^24)*invTraceM < 1/10^12 ∧ 27000*(1/10^24)*invTraceM < 1/10^12 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
