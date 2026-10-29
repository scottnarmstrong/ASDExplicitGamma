module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Scalar spectral inequalities underlying the analytic coarse-matrix bound. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- Every positive eigenvalue has nonnegative reciprocal defect. -/
theorem reciprocal_eigenvalue_defect_nonnegative (x : ℝ) (hx : 0<x) : 0≤x+x⁻¹-2 := by
  apply (mul_nonneg_iff_of_pos_right hx).mp
  field_simp
  nlinarith only [sq_nonneg (x-1)]

/-- Convert a reciprocal eigenvalue defect into the source explicit operator majorant. -/
theorem eigenvalue_bound_of_reciprocal_defect (x T : ℝ) (hx : 0<x) (hT : 0≤T)
    (hdef : x+x⁻¹-2≤2*T) : x≤1+2*T+Real.sqrt (2*T) := by
  have hmul := mul_le_mul_of_nonneg_right hdef hx.le
  have hsq : (x-1)^2≤2*T*x := by
    field_simp at hmul
    nlinarith only [hmul]
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hT)
  have hs0 := Real.sqrt_nonneg (2*T)
  by_contra h
  have hlt : 1+2*T+Real.sqrt (2*T)<x := lt_of_not_ge h
  have hp := mul_pos (sub_pos.mpr hlt) (show 0<x-1+Real.sqrt (2*T) by linarith)
  have ht := mul_nonneg hT hs0
  nlinarith only [hsq,hs,hp,ht]

/-- A reciprocal trace inequality controls every positive eigenvalue by the true trace excess. -/
theorem eigenvalue_bound_of_inverse_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lambda : ι → ℝ) (hpos : ∀ i,0<lambda i)
    (htrace : (∑ i,(lambda i)⁻¹)≤∑ i,lambda i) :
    let T := (∑ i,lambda i)-(Fintype.card ι:ℝ)
    0≤T ∧ ∀ i,lambda i≤1+2*T+Real.sqrt (2*T) := by
  let T := (∑ i,lambda i)-(Fintype.card ι:ℝ)
  have hsum : (∑ i, (lambda i+(lambda i)⁻¹-2))≤2*T := by
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul]
    dsimp [T]
    linarith only [htrace]
  have hnonneg : 0≤∑ i, (lambda i+(lambda i)⁻¹-2) :=
    Finset.sum_nonneg (fun i _ => reciprocal_eigenvalue_defect_nonnegative _ (hpos i))
  have hT : 0≤T := by linarith only [hsum,hnonneg]
  refine ⟨hT,fun i => eigenvalue_bound_of_reciprocal_defect _ T (hpos i) hT ?_⟩
  exact (Finset.single_le_sum (fun j _ => reciprocal_eigenvalue_defect_nonnegative _ (hpos j))
    (Finset.mem_univ i)).trans hsum

end ASDExplicitGamma.Scalar
