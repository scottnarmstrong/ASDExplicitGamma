module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import ASDExplicitGamma.Gaussian.HilbertBasisEnumeration

/-! # Covariance-factor Cameron–Martin carrier with the input Hilbert norm -/

@[expose] public section

open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

section
variable {W F : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (T : W →L[ℝ] F)

/-- The covariance Hilbert carrier uses the input norm on the kernel complement. -/
abbrev CameronMartin := ↥(T.kerᗮ)

omit [CompleteSpace W] in
/-- Any orthonormal family in the genuine covariance Hilbert carrier is orthonormal in
white noise. Hence every physical Hilbert–Schmidt bound applies to every such family. -/
theorem cameronMartin_orthonormal {ι : Type*} (e : ι → CameronMartin T)
    (he : Orthonormal ℝ e) : Orthonormal ℝ (fun i => (e i : W)) :=
  he.comp_linearIsometry T.kerᗮ.subtypeₗᵢ

/-- Parseval on the genuine covariance carrier preserves every observation variance. -/
theorem cameronMartin_basis_variance {ι : Type*}
    (e : HilbertBasis ι ℝ (CameronMartin T)) (l : W →L[ℝ] ℝ)
    (hl : ∀ u, T u = 0 → l u = 0) :
    (∑' j, (l (e j : W)) ^ 2) = ‖(InnerProductSpace.toDual ℝ W).symm l‖ ^ 2 := by
  let z := (InnerProductSpace.toDual ℝ W).symm l
  have hz : z ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hh := congrArg (fun f : W →L[ℝ] ℝ => f u)
      ((InnerProductSpace.toDual ℝ W).apply_symm_apply l)
    change ⟪z, u⟫ = l u at hh
    exact hh.trans (hl u hu)
  let z' : CameronMartin T := ⟨z, hz⟩
  have he (j : ι) : l (e j : W) = ⟪z', e j⟫ := by
    exact (congrArg (fun f : W →L[ℝ] ℝ => f (e j : W))
      ((InnerProductSpace.toDual ℝ W).apply_symm_apply l)).symm
  simp_rw [he]
  have hh := e.tsum_inner_mul_inner z' z'
  have hnorm : ‖z'‖ = ‖(InnerProductSpace.toDual ℝ W).symm l‖ := rfl
  calc
    _ = ∑' j, ⟪z', e j⟫ * ⟪e j, z'⟫ := by
      apply tsum_congr
      intro j
      rw [real_inner_comm (e j) z', sq]
    _ = _ := hh.trans (by rw [real_inner_self_eq_norm_sq, hnorm])

end
end ASDExplicitGamma.Gaussian
