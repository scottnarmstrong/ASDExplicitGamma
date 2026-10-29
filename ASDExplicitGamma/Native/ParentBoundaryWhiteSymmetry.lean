module

public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity
public import Homogenization.Sobolev.H1.OriginCubeSymmetry
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Physical white-noise symmetries for the parent Gram argument.
These transform the complete noise carrier, rather than asserting symmetry
of a finite truncation of an arbitrary chosen white basis. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Reflection of the actual two-dimensional white-noise L2 carrier. -/
def parentBoundaryWhiteFlip (i : Fin 2) : WhiteNoise →ₗᵢ[ℝ] WhiteNoise :=
  Lp.compMeasurePreservingₗᵢ ℝ (signFlipVecContinuousLinearEquiv i)
    (measurePreserving_signFlipVecContinuousLinearEquiv i)

/-- Coordinate swap of the actual white-noise carrier. -/
def parentBoundaryWhiteSwap : WhiteNoise →ₗᵢ[ℝ] WhiteNoise :=
  Lp.compMeasurePreservingₗᵢ ℝ (swapVecContinuousLinearEquiv (0 : Fin 2) 1)
    (measurePreserving_swapVecContinuousLinearEquiv (0 : Fin 2) 1)

/-- The literal q3 value kernel transforms by simultaneous reflection of
its observation and white-noise coordinates. -/
theorem parent_boundary_value_kernel_flip (i : Fin 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (x y : Vec 2) :
    q3SectionFunction b L h3Zero x (signFlipVecContinuousLinearEquiv i y) =
      q3SectionFunction b L h3Zero (signFlipVecContinuousLinearEquiv i x) y := by
  have he (s t : ℝ) : q3Kernel ((s+t)/L.1)=q3Kernel ((-s-t)/L.1) := by
    rw [show (-s-t)/L.1 = -((s+t)/L.1) by ring]
    simp only [q3Kernel,neg_sq,abs_neg]
  fin_cases i <;>
    simp [q3SectionFunction,h3Zero,q3Derivative,
      signFlipVecContinuousLinearEquiv_apply,matVecMul_signFlipMatrix_apply,he]

/-- The product value kernel transforms by simultaneous coordinate swap. -/
theorem parent_boundary_value_kernel_swap (b : ℝ)
    (L : {l : ℝ // 0<l}) (x y : Vec 2) :
    q3SectionFunction b L h3Zero x (swapVecContinuousLinearEquiv (0 : Fin 2) 1 y) =
      q3SectionFunction b L h3Zero (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x) y := by
  simp only [q3SectionFunction,h3Zero,q3Derivative,
    swapVecContinuousLinearEquiv_apply,matVecMul_swap_eq_comp,Function.comp_apply,
    Equiv.swap_apply_left,Equiv.swap_apply_right,Matrix.cons_val_zero]
  ring

/-- Reflection acts on the genuine Hilbert value section. -/
theorem parent_boundary_value_section_flip (i : Fin 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (x : Vec 2) :
    parentBoundaryWhiteFlip i (q3Section b L h3Zero x) =
      q3Section b L h3Zero (signFlipVecContinuousLinearEquiv i x) := by
  apply Lp.ext
  have hmp := measurePreserving_signFlipVecContinuousLinearEquiv i
  filter_upwards [Lp.coeFn_compMeasurePreserving (q3Section b L h3Zero x) hmp,
    hmp.quasiMeasurePreserving.ae_eq_comp (q3SectionFunction_memLp b L h3Zero x).coeFn_toLp,
    (q3SectionFunction_memLp b L h3Zero (signFlipVecContinuousLinearEquiv i x)).coeFn_toLp]
    with y hy hz ht
  exact hy.trans (hz.trans ((parent_boundary_value_kernel_flip i b L x y).trans ht.symm))

/-- Swapping coordinates acts on the complete Hilbert section. -/
theorem parent_boundary_value_section_swap (b : ℝ)
    (L : {l : ℝ // 0<l}) (x : Vec 2) :
    parentBoundaryWhiteSwap (q3Section b L h3Zero x) =
      q3Section b L h3Zero (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x) := by
  apply Lp.ext
  have hmp := measurePreserving_swapVecContinuousLinearEquiv (0 : Fin 2) 1
  filter_upwards [Lp.coeFn_compMeasurePreserving (q3Section b L h3Zero x) hmp,
    hmp.quasiMeasurePreserving.ae_eq_comp (q3SectionFunction_memLp b L h3Zero x).coeFn_toLp,
    (q3SectionFunction_memLp b L h3Zero (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x)).coeFn_toLp]
    with y hy hz ht
  exact hy.trans (hz.trans ((parent_boundary_value_kernel_swap b L x y).trans ht.symm))

/-- The actual convolution with reflected complete white input is the
spatially reflected convolution with the original input. -/
theorem parent_boundary_convolution_flip (i : Fin 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (w : WhiteNoise) (x : Vec 2) :
    q3Convolution b L h3Zero (parentBoundaryWhiteFlip i w) x =
      q3Convolution b L h3Zero w (signFlipVecContinuousLinearEquiv i x) := by
  have hh := (parentBoundaryWhiteFlip i).inner_map_map w
    (q3Section b L h3Zero (signFlipVecContinuousLinearEquiv i x))
  rw [parent_boundary_value_section_flip,signFlipVecContinuousLinearEquiv_self_apply] at hh
  exact hh

/-- The same realization identity for the coordinate swap. -/
theorem parent_boundary_convolution_swap (b : ℝ)
    (L : {l : ℝ // 0<l}) (w : WhiteNoise) (x : Vec 2) :
    q3Convolution b L h3Zero (parentBoundaryWhiteSwap w) x =
      q3Convolution b L h3Zero w (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x) := by
  have hh := parentBoundaryWhiteSwap.inner_map_map w
    (q3Section b L h3Zero (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x))
  rw [parent_boundary_value_section_swap,swapVecContinuousLinearEquiv_self_apply] at hh
  exact hh

end
end ASDExplicitGamma.Native
