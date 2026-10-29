module

public import ASDExplicitGamma.Cold.GramMatrix

/-! # The Euclidean norm of a nonnegative finite-dimensional operator is bounded by its trace -/

@[expose] public section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The exact spectral trace bound, with no norm or eigenvalue estimate assumed. -/
theorem norm_le_trace_of_positive_operator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (H : E →L[ℝ] E)
    (hSym : H.toLinearMap.IsSymmetric) (hPos : ∀ x, 0 ≤ ⟪x,H x⟫) :
    ‖H‖ ≤ LinearMap.trace ℝ E H.toLinearMap := by
  let N := Module.finrank ℝ E
  let b := hSym.eigenvectorBasis (show Module.finrank ℝ E = N from rfl)
  let lambda := hSym.eigenvalues (show Module.finrank ℝ E = N from rfl)
  have hEigen (i : Fin N) : H (b i) = lambda i • b i := hSym.apply_eigenvectorBasis rfl i
  have hNonneg (i : Fin N) : 0 ≤ lambda i := by
    have hp := hPos (b i)
    rw [hEigen,inner_smul_right] at hp
    have hn : ⟪b i,b i⟫ = 1 := by rw [real_inner_self_eq_norm_sq,b.norm_eq_one]; norm_num
    simpa only [hn,mul_one] using hp
  have ht : LinearMap.trace ℝ E H.toLinearMap = ∑ i, lambda i :=
    linearMap_trace_eq_eigenbasis_sum b H.toLinearMap lambda hEigen
  have hsum : 0 ≤ ∑ i, lambda i := Finset.sum_nonneg fun i _ => hNonneg i
  apply ContinuousLinearMap.opNorm_le_bound H (by rw [ht]; exact hsum)
  intro x
  have hs (i : Fin N) : lambda i ^ 2 ≤ (∑ j,lambda j)^2 :=
    pow_le_pow_left₀ (hNonneg i) (Finset.single_le_sum (fun j _ => hNonneg j) (Finset.mem_univ i)) 2
  have hnorm : ‖H x‖^2 = ∑ i, lambda i^2*(b.repr x i)^2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hh : ⟪H x,H x⟫ = ⟪x,H (H x)⟫ := hSym x (H x)
    rw [hh]
    apply inner_apply_eq_eigenbasis_sum b (H.toLinearMap.comp H.toLinearMap) (fun i => lambda i^2)
    intro i
    change H (H (b i)) = lambda i^2 • b i
    rw [hEigen,map_smul,hEigen,smul_smul,pow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by rw [ht]; exact hsum) (norm_nonneg _))).mp
  rw [mul_pow,ht,hnorm,← real_inner_self_eq_norm_sq,← eigenbasis_sum_sq_eq_inner b x,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hs i) (sq_nonneg _)

end ASDExplicitGamma.Cold
