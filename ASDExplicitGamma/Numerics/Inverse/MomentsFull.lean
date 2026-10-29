module

public import ASDExplicitGamma.Numerics.Inverse.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invFullTau : ℚ := 5000000000000000

def invFullQ : ℚ := (310867117301379923 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

def invFullQraw : ℚ := 364*3^80*(3*(61/10)/invFullTau)^12

theorem invFull_density :
    invFullQraw ≤ invFullQ ∧ invFullQ < invFullQraw+1/10^150 ∧ invFullQ < 1/10^10 := by
  decide +kernel

theorem invFull_floor :
    (Nat.factorial 200 : ℚ) < 6000^200*invFullQ := by
  decide +kernel

theorem invFull_cutoff :
    (2718/1000 : ℚ)^307 ≤ 200/(26*invFullQ) ∧ 200/(26*invFullQ) < (2718/1000 : ℚ)^308 := by
  decide +kernel

def invFullM2 : ℚ := (192934391612107325751259 / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invFullM2_formula :
    invFullM2 = 26*invFullQ*((1 : ℚ)*4^0*1232^2 + (2 : ℚ)*4^1*1232^1 + (2 : ℚ)*4^2*1232^0) := by
  decide +kernel

def invFullM4 : ℚ := (4605634580142266488773299409 / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invFullM4_formula :
    invFullM4 = 26*invFullQ*((1 : ℚ)*4^0*1232^4 + (4 : ℚ)*4^1*1232^3 + (12 : ℚ)*4^2*1232^2 + (24 : ℚ)*4^3*1232^1 + (24 : ℚ)*4^4*1232^0) := by
  decide +kernel

def invFullM8 : ℚ := (2624853211948725663215167429399306297 / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem invFullM8_formula :
    invFullM8 = 26*invFullQ*((1 : ℚ)*4^0*1232^8 + (8 : ℚ)*4^1*1232^7 + (56 : ℚ)*4^2*1232^6 + (336 : ℚ)*4^3*1232^5 + (1680 : ℚ)*4^4*1232^4 + (6720 : ℚ)*4^5*1232^3 + (20160 : ℚ)*4^6*1232^2 + (40320 : ℚ)*4^7*1232^1 + (40320 : ℚ)*4^8*1232^0) := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
