module

public import ASDExplicitGamma.Numerics.Inverse.MomentsFull
public import ASDExplicitGamma.Numerics.Inverse.Layers

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invFull128Delta : ℚ := 10/(80*(1+invFullTau))

def invFull128Ed : ℚ := invE ((17444/10000)*(1+invFullTau)*invFull128Delta)

def invFull128C : ℚ := 3*(2700*3^80+1)

def invFull128SelectedRoot : ℚ := (10196029973038112351309133886606669573988566325891042851348086118817461142479994620459805396533465743 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFull128Vroot : ℚ := (687747462234169731065933300552714355598639975094253203498690103749930864041 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFull128Droot : ℚ := (256594908756974365654578402120607619375681265068393458397176771661038500892164701129014314228407286957041 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFull128M4root : ℚ := (43433488508595212237300093504142163495719 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invFull128_selected_root :
    invFull128SelectedRoot^128 > (12 : ℚ) := by
  decide +kernel

theorem invFull128_radicals :
    0 < invFull128M4root ∧ invFullM4 < invFull128M4root^2 ∧ 0 < invFull128Droot ∧ (4*128*63^2*12^4 : ℚ) < invFull128Droot^2 ∧ 0 < invFull128Vroot ∧ 16*128*63^2*invFullM8 < invFull128Vroot^4 := by
  decide +kernel

def invFull128M0 : ℚ := (2/3)*(1/3^336)/(66/100)^2

def invFull128Z0 : ℚ := (1/3^166)/(41/100)^2

def invFull128D4 : ℚ := (2700*3^80+1)*9*(invFull128Vroot*(1/3^136)/(35/100)^2+invFull128Droot*(1/3^166)/(41/100)^2+(1/3^336)/(66/100)^2)

def invFull128MC : ℚ := 4*16*4*12*(2*invFullTau+2)

def invFull128c0 : ℚ := 2*(1+2*invFull128Delta)^2*(1+6*invFullTau)

def invFull128c1 : ℚ := 2*(1+6*invFullTau)

def invFull128J : ℚ := invE (11/5*invGamma*350)+1/10^100

def invFull128W : ℚ := 40*(2*128+2)*invFull128SelectedRoot*invE (22/5*invGamma*350)

def invFull128W0 : ℚ := invFull128W+1/10^100

def invFull128W1 : ℚ := 350*invFull128W+351/10^100

def invFull128mx : ℚ := invFull128Ed*80*(128+2)*invFull128MC*invFull128M0

def invFull128de : ℚ := invFull128Ed*40*(2*128+2)*invFull128c1*invFull128D4

def invFull128Bt : ℚ := invFull128Ed*((1.16+invFull128C*invFull128c0*invFullM2)*invLayer (2*invGamma)*invFull128J+2*invFull128MC*invFull128M0+3*invFull128C*invFull128c0*invFull128Z0)

def invFull128KD : ℚ := invFull128Ed*((1.16/4)*invFull128W0*invLayer (4*invGamma)+invFull128C*invFull128c1*invFull128M4root*invFull128W0*invL0)+invFull128mx+invFull128de

def invFull128K0 : ℚ := invFull128Ed*((1.16/4)*(invFull128W0*invLayerF (4*invGamma)+invFull128W1*invLayer (4*invGamma))+invFull128C*invFull128c1*invFull128M4root*(invFull128W0*invL1+invFull128W1*invL0))+350*(invFull128mx+invFull128de)

theorem invFull128_caps :
    invFull128Bt < 2.018618 ∧ invFull128KD < 32474 ∧ invFull128K0 < 11483216 := by
  decide +kernel

theorem invFull128_layer_combination :
    invFull128W1-350*invFull128W0 = 1/10^100 ∧ invFull128W0*invL1plus+invFull128W1*invL0plus < invFull128W0*invL1+invFull128W1*invL0 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
