module

public import ASDExplicitGamma.Main.Q3SectionGram
public import ASDExplicitGamma.Main.CMCovariance
public import ASDExplicitGamma.Model.Q3DerivativeGram

/-! Same-point actual q3 jets identified with the source covariance rows. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped RealInnerProductSpace

/-- Spatial jet indices of order at most two in the actual convolution factor. -/
def mainQ3JetIndex (o : Q3SpatialJet) : H3Index :=
  ⟨(⟨o.count 0, by cases o with
      | value => decide
      | first i => fin_cases i <;> decide
      | second i j => fin_cases i <;> fin_cases j <;> decide⟩,
    ⟨o.count 1, by cases o with
      | value => decide
      | first i => fin_cases i <;> decide
      | second i j => fin_cases i <;> fin_cases j <;> decide⟩), by
    cases o with
    | value => decide
    | first i => fin_cases i <;> decide
    | second i j => fin_cases i <;> fin_cases j <;> decide⟩

/-- The exact same-point Gram rows contain the source derivative operator
constants, including the signed value--Hessian cross covariance. -/
theorem main_q3_jet_gram (b : ℝ) (L : {l : ℝ // 0 < l})
    (o p : Q3SpatialJet) (x : Vec 2) :
    ⟪q3Section b L (mainQ3JetIndex o) x, q3Section b L (mainQ3JetIndex p) x⟫ =
      q3ScaledJetCovariance (b^2) L.1 o p x x := by
  have ha (q : Q3SpatialJet) : (mainQ3JetIndex q).1.1.val < 3 ∧
      (mainQ3JetIndex q).1.2.val < 3 := by
    cases q with
    | value => exact ⟨by decide, by decide⟩
    | first i => fin_cases i <;> exact ⟨by decide, by decide⟩
    | second i j => fin_cases i <;> fin_cases j <;> exact ⟨by decide, by decide⟩
  rw [main_q3_section_gram b L _ _ (ha o).1 (ha o).2 (ha p).1 (ha p).2]
  cases o
  all_goals first
    | (rename_i i j; fin_cases i <;> fin_cases j)
    | (rename_i i; fin_cases i)
    | skip
  all_goals cases p
  all_goals first
    | (rename_i i j; fin_cases i <;> fin_cases j)
    | (rename_i i; fin_cases i)
    | skip
  all_goals norm_num [mainQ3JetIndex, mainQ3KernelGram, q3DerivativeMoment,
    q3ScaledJetCovariance, Q3SpatialJet.order, Q3SpatialJet.count, q3CovariancePartial_eq,
    q3Cov_at_zero, q3Cov_iteratedDeriv_values.1, q3Cov_iteratedDeriv_values.2.1,
    q3Cov_odd_derivatives_zero.1, q3Cov_odd_derivatives_zero.2]
  all_goals field_simp [L.2.ne']
  all_goals ring

end ASDExplicitGamma.Main
