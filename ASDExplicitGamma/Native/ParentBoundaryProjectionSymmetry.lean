module

public import ASDExplicitGamma.Native.ParentBoundaryWhiteSymmetry
public import ASDExplicitGamma.Scalar.Lambda8LocalProjection
public import Homogenization.Ambient.CoefficientFieldHilbert

/-! Isometries of the actual vector L2 projection carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar
noncomputable section

/-- A pointwise Hilbert isometry lifts to the actual L2 carrier. -/
def parentBoundaryPointwiseIsometry {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (mu : Measure X) (V : E →L[ℝ] E) (hV : ∀ z, ‖V z‖=‖z‖) :
    Lp E 2 mu →ₗᵢ[ℝ] Lp E 2 mu where
  toLinearMap := (V.compLpL 2 mu).toLinearMap
  norm_map' f := by
    have ha := V.coeFn_compLp f
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [ha] with x hx
      change ‖(V.compLp f) x‖ ≤ ‖f x‖
      rw [hx,hV]
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [ha] with x hx
      change ‖f x‖ ≤ ‖(V.compLp f) x‖
      rw [hx,hV]

/-- Concrete coordinate reflection on the planar Hilbert carrier. -/
def parentBoundaryHilbertFlip (i : Fin 2) : HilbertVec 2 →L[ℝ] HilbertVec 2 :=
  HilbertVec.applyMat (signFlipMatrix i)

/-- Reflection preserves the physical Euclidean vector norm. -/
theorem parent_boundary_hilbert_flip_norm (i : Fin 2) (z : HilbertVec 2) :
    ‖parentBoundaryHilbertFlip i z‖=‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [parentBoundaryHilbertFlip,HilbertVec.norm_sq_applyMat]
  rw [HilbertVec.norm_sq_eq_vecDot]
  simp only [vecDot,matVecMul_signFlipMatrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

/-- Concrete coordinate swap on the planar Hilbert carrier. -/
def parentBoundaryHilbertSwap : HilbertVec 2 →L[ℝ] HilbertVec 2 :=
  HilbertVec.applyMat (Matrix.swap ℝ 0 1)

/-- The coordinate swap preserves the physical Euclidean norm. -/
theorem parent_boundary_hilbert_swap_norm (z : HilbertVec 2) :
    ‖parentBoundaryHilbertSwap z‖=‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [parentBoundaryHilbertSwap,HilbertVec.norm_sq_applyMat]
  rw [HilbertVec.norm_sq_eq_vecDot]
  simp [vecDot,matVecMul_swap_eq_comp,Fin.sum_univ_two]
  ring

/-- Simultaneous reflection of the domain and vector components on the
actual origin-square L2 carrier. -/
def parentBoundaryVectorFlip (m : ℤ) (i : Fin 2) :
    HilbertVectorL2 (openCubeSet (originCube 2 m)) →ₗᵢ[ℝ]
      HilbertVectorL2 (openCubeSet (originCube 2 m)) :=
  (parentBoundaryPointwiseIsometry (volume.restrict (openCubeSet (originCube 2 m)))
    (parentBoundaryHilbertFlip i) (parent_boundary_hilbert_flip_norm i)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (signFlipVecContinuousLinearEquiv i)
      (measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i m))

/-- Simultaneous domain and vector-coordinate swap on that same carrier. -/
def parentBoundaryVectorSwap (m : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube 2 m)) →ₗᵢ[ℝ]
      HilbertVectorL2 (openCubeSet (originCube 2 m)) :=
  (parentBoundaryPointwiseIsometry (volume.restrict (openCubeSet (originCube 2 m)))
    parentBoundaryHilbertSwap parent_boundary_hilbert_swap_norm).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (swapVecContinuousLinearEquiv (0 : Fin 2) 1)
      (measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube (0 : Fin 2) 1 m))

/-- Reflection on the L2 class has the literal simultaneous field action. -/
theorem parent_boundary_vector_flip_coeFn (m : ℤ) (i : Fin 2)
    (F : HilbertVectorL2 (openCubeSet (originCube 2 m))) :
    parentBoundaryVectorFlip m i F =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
      fun x => HilbertVec.ofVec (signFlipVecContinuousLinearEquiv i
        (F (signFlipVecContinuousLinearEquiv i x)).toVec) := by
  have hmp := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i m
  have ha := (parentBoundaryHilbertFlip i).coeFn_compLp (Lp.compMeasurePreserving _ hmp F)
  filter_upwards [ha,Lp.coeFn_compMeasurePreserving F hmp] with x hx hy
  change (parentBoundaryVectorFlip m i F) x = _ at hx
  rw [hx,hy]
  simp only [parentBoundaryHilbertFlip,HilbertVec.applyMat_apply,
    Function.comp_apply,signFlipVecContinuousLinearEquiv_apply]

/-- Coordinate swap on the L2 class has its literal simultaneous action. -/
theorem parent_boundary_vector_swap_coeFn (m : ℤ)
    (F : HilbertVectorL2 (openCubeSet (originCube 2 m))) :
    parentBoundaryVectorSwap m F =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
      fun x => HilbertVec.ofVec (swapVecContinuousLinearEquiv (0 : Fin 2) 1
        (F (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x)).toVec) := by
  have hmp := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube (0 : Fin 2) 1 m
  have ha := parentBoundaryHilbertSwap.coeFn_compLp (Lp.compMeasurePreserving _ hmp F)
  filter_upwards [ha,Lp.coeFn_compMeasurePreserving F hmp] with x hx hy
  change (parentBoundaryVectorSwap m F) x = _ at hx
  rw [hx,hy]
  simp only [parentBoundaryHilbertSwap,HilbertVec.applyMat_apply,
    Function.comp_apply,swapVecContinuousLinearEquiv_apply]

/-- An involutive isometry preserving the genuine gradient subspace
commutes with its actual orthogonal projection. -/
theorem parent_boundary_projection_commutes {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : Submodule ℝ E) [p.HasOrthogonalProjection]
    (T : E →ₗᵢ[ℝ] E) (hT : Function.Involutive T)
    (hp : ∀ y ∈ p, T y ∈ p) (x : E) :
    T (p.starProjection x)=p.starProjection (T x) := by
  apply (p.eq_starProjection_of_mem_of_inner_eq_zero
    (hp _ (p.starProjection_apply_mem x)) ?_).symm
  intro y hy
  have hh := p.starProjection_inner_eq_zero x (T y) (hp y hy)
  have he := T.inner_map_map (x-p.starProjection x) (T y)
  rw [hT, T.map_sub] at he
  exact he.trans hh

end
end ASDExplicitGamma.Native
