module

public import ASDExplicitGamma.Numerics.Inverse.ProfileFirst
public import ASDExplicitGamma.Numerics.Inverse.ProfileGlobal
public import ASDExplicitGamma.Numerics.Inverse.ProfileLocal
public import ASDExplicitGamma.Numerics.Inverse.Full64
public import ASDExplicitGamma.Numerics.Inverse.Full128
public import ASDExplicitGamma.Numerics.Inverse.FullHistory
public import Mathlib.Basic.Real.Basic

/-! Real-valued forms of the certified numerical profile outputs used by the
inverse-bank consumers. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse

theorem bank_first_local_profile_bounds :
    ((invFirstA + invFirste : ℚ) : ℝ) < ((159 / 100 : ℚ) : ℝ) ∧
    ((invFirstA + 1 / 2000 : ℚ) : ℝ) < ((159 / 100 : ℚ) : ℝ) ∧
    ((invFirste ^ 2 / (4 * (1 / 2000)) : ℚ) : ℝ) <
      ((3 / 10000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  exact_mod_cast invFirst_outputs

theorem bank_global_profile_bounds :
    ((invGlobalA + invGlobale : ℚ) : ℝ) < ((14103 / 10000 : ℚ) : ℝ) ∧
    ((invGlobalA + 1 / 2000 : ℚ) : ℝ) < ((14103 / 10000 : ℚ) : ℝ) ∧
    ((invGlobale ^ 2 / (4 * (1 / 2000)) : ℚ) : ℝ) <
      ((1 / 1000000000000000000000000 : ℚ) : ℝ) := by
  exact_mod_cast invGlobal_outputs

theorem bank_local_profile_bounds :
    ((invLocalA + invLocale : ℚ) : ℝ) < ((3683 / 2500 : ℚ) : ℝ) ∧
    ((invLocalA + 1 / 2000 : ℚ) : ℝ) < ((3683 / 2500 : ℚ) : ℝ) ∧
    ((invLocale ^ 2 / (4 * (1 / 2000)) : ℚ) : ℝ) <
      ((3 / 10000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  exact_mod_cast invLocal_outputs

theorem bank_full_response_64_caps :
    ((invFull64Bt : ℚ) : ℝ) < ((2.018618 : ℚ) : ℝ) ∧
    ((invFull64KD : ℚ) : ℝ) < ((16684 : ℚ) : ℝ) ∧
    ((invFull64K0 : ℚ) : ℝ) < ((5899542 : ℚ) : ℝ) := by
  exact_mod_cast invFull64_caps

theorem bank_full_response_128_caps :
    ((invFull128Bt : ℚ) : ℝ) < ((2.018618 : ℚ) : ℝ) ∧
    ((invFull128KD : ℚ) : ℝ) < ((32474 : ℚ) : ℝ) ∧
    ((invFull128K0 : ℚ) : ℝ) < ((11483216 : ℚ) : ℝ) := by
  exact_mod_cast invFull128_caps

theorem bank_full_response_positive_history_bound :
    ((invFullB0 + invFulle : ℚ) : ℝ) < ((2.031006 : ℚ) : ℝ) ∧
    ((invFulle ^ 2 / (4 * (1 / 2000)) : ℚ) : ℝ) < ((1 / 10 ^ 34 : ℚ) : ℝ) := by
  exact_mod_cast invFull_positive_history

end ASDExplicitGamma.Inverse
