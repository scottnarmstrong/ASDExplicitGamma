module

public import ASDExplicitGamma.Inverse.BankPopulationArithmetic
public import ASDExplicitGamma.Inverse.BankProfileArithmetic

/-! The three source inverse-bank rows, with their exact certified profiles. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Numerics.Inverse

inductive InverseBankRow where
  | firstLocal | globalInverse | localInverse
  deriving DecidableEq

def inverseBankRootRow : InverseBankRow → RootRow
  | .firstLocal => .firstLocal
  | .globalInverse => .globalInverse
  | .localInverse => .localInverse

def inverseBankLi : InverseBankRow → ℚ
  | .firstLocal => invFirstLi
  | .globalInverse => invGlobalLi
  | .localInverse => invLocalLi

def inverseBankRho : InverseBankRow → ℚ
  | .firstLocal => invFirstRho
  | .globalInverse => invGlobalRho
  | .localInverse => invLocalRho

def inverseBankHeight : InverseBankRow → ℕ
  | .globalInverse => 306
  | _ => 350

def inverseBankA : InverseBankRow → ℚ
  | .firstLocal => invFirstA
  | .globalInverse => invGlobalA
  | .localInverse => invLocalA

def inverseBankE : InverseBankRow → ℚ
  | .firstLocal => invFirste
  | .globalInverse => invGlobale
  | .localInverse => invLocale

def inverseBankCap : InverseBankRow → ℚ
  | .firstLocal => 159/100
  | .globalInverse => 14103/10000
  | .localInverse => 3683/2500

def inverseBankReserve : InverseBankRow → ℚ
  | .globalInverse => 1/10^24
  | _ => 3/10^46

theorem inverse_bank_source_formulas (r : InverseBankRow) :
    inverseBankA r = invE (11/5*invGamma)*invE (11*invGamma)*inverseBankLi r*
        invE (11/5*invGamma*inverseBankHeight r)*invSB ∧
      inverseBankE r = invE (11/5*invGamma)*(509/500)*invE (11*invGamma)*
        invPopulationRoot*inverseBankRho r*invSR := by
  cases r <;> exact ⟨rfl,rfl⟩

theorem inverse_bank_profile_nonneg (r : InverseBankRow) :
    0 ≤ (inverseBankA r:ℝ) ∧ 0 ≤ (inverseBankE r:ℝ) ∧
      0 ≤ (inverseBankLi r:ℝ) ∧ 0 ≤ (inverseBankRho r:ℝ) ∧
      0 ≤ (invE (11/5*invGamma*inverseBankHeight r):ℝ) := by
  have hq : 0 ≤ inverseBankA r ∧ 0 ≤ inverseBankE r ∧
      0 ≤ inverseBankLi r ∧ 0 ≤ inverseBankRho r ∧
      0 ≤ invE (11/5*invGamma*inverseBankHeight r) := by
    cases r <;> decide +kernel
  exact ⟨(Rat.cast_nonneg (K := ℝ)).2 hq.1,
    (Rat.cast_nonneg (K := ℝ)).2 hq.2.1,
    (Rat.cast_nonneg (K := ℝ)).2 hq.2.2.1,
    (Rat.cast_nonneg (K := ℝ)).2 hq.2.2.2.1,
    (Rat.cast_nonneg (K := ℝ)).2 hq.2.2.2.2⟩

theorem inverse_bank_Li_bound (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (r : InverseBankRow) :
    rootLi M.gamma (inverseBankRootRow r) ≤ (inverseBankLi r:ℝ) := by
  have hg' : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  cases r with
  | firstLocal => exact bank_first_root_Li_bound _ M.shellPrefix.gamma_pos.le hg'
  | globalInverse => exact bank_global_root_Li_bound _ M.shellPrefix.gamma_pos.le hg'
  | localInverse => exact bank_local_root_Li_bound _ M.shellPrefix.gamma_pos.le hg'

theorem inverse_bank_height_bound (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (r : InverseBankRow) :
    (3:ℝ)^(2*M.gamma*((rootH0 (inverseBankRootRow r):ℝ)-27)) ≤
      (invE (11/5*invGamma*inverseBankHeight r):ℝ) := by
  have hg' : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hh := bank_history_height_cap M.gamma (inverseBankHeight r)
    M.shellPrefix.gamma_pos.le hg' (by cases r <;> norm_num [inverseBankHeight])
  have he : (rootH0 (inverseBankRootRow r):ℝ)-27 = (inverseBankHeight r:ℝ) := by
    cases r <;> norm_num [inverseBankRootRow, inverseBankHeight, rootH0]
  simpa only [he] using hh

theorem inverse_bank_error_bound (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (r : InverseBankRow) :
    rootLi M.gamma (inverseBankRootRow r)*
        selectedRootTiny (rootH0 (inverseBankRootRow r)) +
      (rootMatrixErrorBudget M.gamma 256 (inverseBankRootRow r)+
        rootDensityErrorBudget M.gamma (inverseBankRootRow r)) ≤ (inverseBankRho r:ℝ) := by
  have hg' : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  cases r with
  | firstLocal => exact bank_first_root_error_plus_tiny_bound _ M.shellPrefix.gamma_pos.le hg'
  | globalInverse => exact bank_global_root_error_plus_tiny_bound _ M.shellPrefix.gamma_pos.le hg'
  | localInverse => exact bank_local_root_error_plus_tiny_bound _ M.shellPrefix.gamma_pos.le hg'

theorem inverse_bank_numeric_bounds (r : InverseBankRow) :
    (inverseBankA r:ℝ)+(inverseBankE r:ℝ) < (inverseBankCap r:ℝ) ∧
      (inverseBankA r:ℝ)+(1/2000:ℝ) < (inverseBankCap r:ℝ) ∧
      (inverseBankE r:ℝ)^2/(4*(1/2000:ℝ)) < (inverseBankReserve r:ℝ) := by
  cases r with
  | firstLocal =>
    have hh := bank_first_local_profile_bounds
    norm_num [inverseBankA, inverseBankE, inverseBankCap, inverseBankReserve,
      Rat.cast_add, Rat.cast_pow, Rat.cast_div, Rat.cast_mul] at hh ⊢
    exact hh

  | globalInverse =>
    have hh := bank_global_profile_bounds
    norm_num [inverseBankA, inverseBankE, inverseBankCap, inverseBankReserve,
      Rat.cast_add, Rat.cast_pow, Rat.cast_div, Rat.cast_mul] at hh ⊢
    exact hh
  | localInverse =>
    have hh := bank_local_profile_bounds
    norm_num [inverseBankA, inverseBankE, inverseBankCap, inverseBankReserve,
      Rat.cast_add, Rat.cast_pow, Rat.cast_div, Rat.cast_mul] at hh ⊢
    exact hh

theorem inverse_bank_grouped_numeric_bound (r : InverseBankRow) :
    (inverseBankA r:ℝ)+(1/2000:ℝ)+5*(inverseBankReserve r:ℝ) < (inverseBankCap r:ℝ) := by
  have hq : inverseBankA r+1/2000+5*inverseBankReserve r < inverseBankCap r := by
    cases r <;> decide +kernel
  have hh := (Rat.cast_lt (K := ℝ)).2 hq
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh

end ASDExplicitGamma.Inverse
