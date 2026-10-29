module

public import ASDExplicitGamma.Numerics.Inverse.MomentsFull
public import ASDExplicitGamma.Numerics.Inverse.Layers

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invFull64Delta : ℚ := 10/(80*(1+invFullTau))

def invFull64Ed : ℚ := invE ((17444/10000)*(1+invFullTau)*invFull64Delta)

def invFull64C : ℚ := 3*(2700*3^80+1)

def invFull64SelectedRoot : ℚ := (5197951360554578504079016117217274165783469288775270417548068335044786697085633118914559656782617719 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFull64Vroot : ℚ := (231329750237021100182566416262377879569342434807067455354423874640427465299 / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFull64Droot : ℚ := (1451520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFull64M4root : ℚ := (43433488508595212237300093504142163495719 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invFull64_selected_root :
    invFull64SelectedRoot^64 > (12 : ℚ) := by
  decide +kernel

theorem invFull64_radicals :
    0 < invFull64M4root ∧ invFullM4 < invFull64M4root^2 ∧ 0 < invFull64Droot ∧ (4*64*63^2*12^4 : ℚ) < invFull64Droot^2 ∧ 0 < invFull64Vroot ∧ 16*64*63^2*invFullM8 < invFull64Vroot^4 := by
  decide +kernel

def invFull64M0 : ℚ := (2/3)*(1/3^336)/(66/100)^2

def invFull64Z0 : ℚ := (1/3^166)/(41/100)^2

def invFull64D4 : ℚ := (2700*3^80+1)*9*(invFull64Vroot*(1/3^136)/(35/100)^2+invFull64Droot*(1/3^166)/(41/100)^2+(1/3^336)/(66/100)^2)

def invFull64MC : ℚ := 4*16*4*8*(2*invFullTau+2)

def invFull64c0 : ℚ := 2*(1+2*invFull64Delta)^2*(1+6*invFullTau)

def invFull64c1 : ℚ := 2*(1+6*invFullTau)

def invFull64J : ℚ := invE (11/5*invGamma*350)+1/10^100

def invFull64W : ℚ := 40*(2*64+2)*invFull64SelectedRoot*invE (22/5*invGamma*350)

def invFull64W0 : ℚ := invFull64W+1/10^100

def invFull64W1 : ℚ := 350*invFull64W+351/10^100

def invFull64mx : ℚ := invFull64Ed*80*(64+2)*invFull64MC*invFull64M0

def invFull64de : ℚ := invFull64Ed*40*(2*64+2)*invFull64c1*invFull64D4

def invFull64Bt : ℚ := invFull64Ed*((1.16+invFull64C*invFull64c0*invFullM2)*invLayer (2*invGamma)*invFull64J+2*invFull64MC*invFull64M0+3*invFull64C*invFull64c0*invFull64Z0)

def invFull64KD : ℚ := invFull64Ed*((1.16/4)*invFull64W0*invLayer (4*invGamma)+invFull64C*invFull64c1*invFull64M4root*invFull64W0*invL0)+invFull64mx+invFull64de

def invFull64K0 : ℚ := invFull64Ed*((1.16/4)*(invFull64W0*invLayerF (4*invGamma)+invFull64W1*invLayer (4*invGamma))+invFull64C*invFull64c1*invFull64M4root*(invFull64W0*invL1+invFull64W1*invL0))+350*(invFull64mx+invFull64de)

theorem invFull64_caps :
    invFull64Bt < 2.018618 ∧ invFull64KD < 16684 ∧ invFull64K0 < 5899542 := by
  decide +kernel

theorem invFull64_layer_combination :
    invFull64W1-350*invFull64W0 = 1/10^100 ∧ invFull64W0*invL1plus+invFull64W1*invL0plus < invFull64W0*invL1+invFull64W1*invL0 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
