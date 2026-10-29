module

public import ASDExplicitGamma.Response.LinearShear

/-! Hilbert direct-sum duality for the negative projected-adjoint Hessian term. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open scoped BigOperators

/-- A row bound on all finite families of compatible variations controls the
sum of squared projected adjoint sources. The proof uses the projected
adjoint family itself as the dual test, which is the direct-sum step needed
for the inverse-trace lower generator. -/
theorem main_projected_adjoint_row_norm_sq_le
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : ClosedSubmodule ℝ E) (C : ι → E →L[ℝ] E) (S : E)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrow : ∀ z : ι → V.toSubmodule,
      |∑ i, inner ℝ S (C i (z i : E))| ≤
        κ * Real.sqrt (∑ i, ‖(z i : E)‖ ^ 2)) :
    (∑ i, ‖(V.toSubmodule.orthogonalProjectionOnto
      ((C i).adjoint S) : E)‖ ^ 2) ≤ κ ^ 2 := by
  let z : ι → V.toSubmodule := fun i =>
    V.toSubmodule.orthogonalProjectionOnto ((C i).adjoint S)
  let X : ℝ := ∑ i, ‖(z i : E)‖ ^ 2
  have hX : 0 ≤ X := by
    dsimp [X]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hpair (i : ι) : inner ℝ S (C i (z i : E)) = ‖(z i : E)‖ ^ 2 := by
    calc
      inner ℝ S (C i (z i : E)) = inner ℝ (C i (z i : E)) S :=
        real_inner_comm _ _
      _ = inner ℝ ((C i).adjoint S) (z i : E) := by
        rw [real_inner_comm]
        exact (ContinuousLinearMap.adjoint_inner_left (C i) (z i : E) S).symm
      _ = inner ℝ ((z i : E)) ((z i : E)) :=
        (V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right
          (z i) ((C i).adjoint S)).symm
      _ = ‖(z i : E)‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hsum : (∑ i, inner ℝ S (C i (z i : E))) = X := by
    dsimp [X]
    exact Finset.sum_congr rfl fun i _ => hpair i
  have hbound := hrow z
  rw [hsum, abs_of_nonneg hX] at hbound
  have hRhs : 0 ≤ κ * Real.sqrt X := mul_nonneg hκ (Real.sqrt_nonneg _)
  have hsquare := (sq_le_sq₀ hX hRhs).mpr hbound
  have hXsq : X ^ 2 ≤ κ ^ 2 * X := by
    rw [mul_pow, Real.sq_sqrt hX] at hsquare
    nlinarith [hsquare]
  have hprojSq :
      (∑ i, ‖(V.toSubmodule.orthogonalProjectionOnto
        ((C i).adjoint S) : E)‖ ^ 2) = X := by
    rfl
  by_cases hX0 : X = 0
  · rw [hprojSq, hX0]
    exact sq_nonneg κ
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
    by_contra hnot
    have hlarge : κ ^ 2 < X := lt_of_not_ge hnot
    have hprod : 0 < X * (X - κ ^ 2) :=
      mul_pos hXpos (sub_pos.mpr hlarge)
    nlinarith [hXsq, hprod]

end ASDExplicitGamma.Main
