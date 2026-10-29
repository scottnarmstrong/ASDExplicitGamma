module

public import ASDExplicitGamma.Native.ParentBoundaryWhiteSymmetry

/-! Complete physical-white bases after square symmetries. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
noncomputable section

/-- Reflection of the actual white carrier is an involution. -/
theorem parent_boundary_white_flip_involutive (i : Fin 2) :
    Function.Involutive (parentBoundaryWhiteFlip i) := by
  intro w
  apply Lp.ext
  have hmp := measurePreserving_signFlipVecContinuousLinearEquiv i
  filter_upwards [Lp.coeFn_compMeasurePreserving (parentBoundaryWhiteFlip i w) hmp,
    hmp.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving w hmp)] with x hx hy
  change (parentBoundaryWhiteFlip i (parentBoundaryWhiteFlip i w)) x = _ at hx
  change (parentBoundaryWhiteFlip i w) (signFlipVecContinuousLinearEquiv i x) = _ at hy
  simp only [Function.comp_apply] at hx hy
  rw [hx,hy]
  simp only [signFlipVecContinuousLinearEquiv_self_apply]

/-- Swapping white coordinates is an involution. -/
theorem parent_boundary_white_swap_involutive :
    Function.Involutive parentBoundaryWhiteSwap := by
  intro w
  apply Lp.ext
  have hmp := measurePreserving_swapVecContinuousLinearEquiv (0 : Fin 2) 1
  filter_upwards [Lp.coeFn_compMeasurePreserving (parentBoundaryWhiteSwap w) hmp,
    hmp.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving w hmp)] with x hx hy
  change (parentBoundaryWhiteSwap (parentBoundaryWhiteSwap w)) x = _ at hx
  change (parentBoundaryWhiteSwap w) (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x) = _ at hy
  simp only [Function.comp_apply] at hx hy
  rw [hx,hy]
  simp only [swapVecContinuousLinearEquiv_self_apply]

/-- Reflection as an isometric equivalence, so it maps a COMPLETE basis
to another complete basis. -/
def parentBoundaryWhiteFlipEquiv (i : Fin 2) : WhiteNoise ≃ₗᵢ[ℝ] WhiteNoise :=
  LinearIsometryEquiv.ofSurjective (parentBoundaryWhiteFlip i)
    (parent_boundary_white_flip_involutive i).surjective

/-- The swap also gives an actual complete-white isometric equivalence. -/
def parentBoundaryWhiteSwapEquiv : WhiteNoise ≃ₗᵢ[ℝ] WhiteNoise :=
  LinearIsometryEquiv.ofSurjective parentBoundaryWhiteSwap
    parent_boundary_white_swap_involutive.surjective

end
end ASDExplicitGamma.Native
