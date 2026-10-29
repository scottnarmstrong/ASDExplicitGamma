module

public import ASDExplicitGamma.Numerics.Inverse.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invGlobalTail : ℚ := (1000/999)*invE ((11/10)*512*invGamma*307/1024)^1024*(Nat.factorial 512)/(3^46/32)^512

theorem invGlobal_tail :
    invGlobalTail < (1/10^30 : ℚ)^256 := by
  decide +kernel

theorem invGlobal_wave_tail_64 :
    40*(4*64+2)*(1000/999)*invE ((11/10)*4*invGamma*307)*(Nat.factorial 512)/((3^46/32)/(2*64))^512 < (1/10^30 : ℚ)^256 := by
  decide +kernel

def invLocalTail : ℚ := (1000/999)*invE ((11/10)*512*invGamma*351/1024)^1024*(Nat.factorial 512)/(3^57/32)^512

theorem invLocal_tail :
    invLocalTail < (1/10^40 : ℚ)^256 := by
  decide +kernel

theorem invLocal_wave_tail_64 :
    40*(4*64+2)*(1000/999)*invE ((11/10)*4*invGamma*351)*(Nat.factorial 512)/((3^57/32)/(2*64))^512 < (1/10^40 : ℚ)^256 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
