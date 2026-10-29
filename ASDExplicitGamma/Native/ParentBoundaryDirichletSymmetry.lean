module

public import ASDExplicitGamma.Native.ParentBoundaryProjectionSymmetry

/-! The genuine Dirichlet projection commutes with the physical square
symmetries. Chosen H10 representatives are compared only through their
actual Hilbert gradients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar
noncomputable section

/-- Simultaneous field reflection is an involution on the actual L2 class. -/
theorem parent_boundary_vector_flip_involutive (m : ℤ) (i : Fin 2) :
    Function.Involutive (parentBoundaryVectorFlip m i) := by
  intro F
  apply Lp.ext
  have hmp := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i m
  filter_upwards [parent_boundary_vector_flip_coeFn m i (parentBoundaryVectorFlip m i F),
    hmp.quasiMeasurePreserving.ae_eq_comp (parent_boundary_vector_flip_coeFn m i F)]
    with x hx hy
  change (parentBoundaryVectorFlip m i F) (signFlipVecContinuousLinearEquiv i x) = _ at hy
  rw [hx,hy]
  simp only [Function.comp_apply,HilbertVec.toVec_ofVec,
    signFlipVecContinuousLinearEquiv_self_apply,HilbertVec.ofVec_toVec]

/-- Simultaneous field swap is an involution. -/
theorem parent_boundary_vector_swap_involutive (m : ℤ) :
    Function.Involutive (parentBoundaryVectorSwap m) := by
  intro F
  apply Lp.ext
  have hmp := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube (0 : Fin 2) 1 m
  filter_upwards [parent_boundary_vector_swap_coeFn m (parentBoundaryVectorSwap m F),
    hmp.quasiMeasurePreserving.ae_eq_comp (parent_boundary_vector_swap_coeFn m F)]
    with x hx hy
  change (parentBoundaryVectorSwap m F) (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x) = _ at hy
  rw [hx,hy]
  simp only [Function.comp_apply,HilbertVec.toVec_ofVec,
    swapVecContinuousLinearEquiv_self_apply,HilbertVec.ofVec_toVec]

/-- Reflection transports an honest H10 gradient to the gradient of its
honest reflected H10 potential. -/
theorem parent_boundary_h10_gradient_flip (m : ℤ) (i : Fin 2)
    (u : H10Function (openCubeSet (originCube 2 m))) :
    parentBoundaryVectorFlip m i u.toH1Function.gradToHilbertVectorL2 =
      (u.signFlipOnOpenCubeSetOriginCube i).toH1Function.gradToHilbertVectorL2 := by
  apply Lp.ext
  have hmp := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i m
  filter_upwards [parent_boundary_vector_flip_coeFn m i u.toH1Function.gradToHilbertVectorL2,
    hmp.quasiMeasurePreserving.ae_eq_comp u.toH1Function.coeFn_gradToHilbertVectorL2,
    (u.signFlipOnOpenCubeSetOriginCube i).toH1Function.coeFn_gradToHilbertVectorL2]
    with x hx hy hz
  change u.toH1Function.gradToHilbertVectorL2 (signFlipVecContinuousLinearEquiv i x) = _ at hy
  rw [hx,hy,hz]
  rfl

/-- The corresponding exact gradient identity for coordinate swap. -/
theorem parent_boundary_h10_gradient_swap (m : ℤ)
    (u : H10Function (openCubeSet (originCube 2 m))) :
    parentBoundaryVectorSwap m u.toH1Function.gradToHilbertVectorL2 =
      (u.swapOnOpenCubeSetOriginCube 0 1).toH1Function.gradToHilbertVectorL2 := by
  apply Lp.ext
  have hmp := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube (0 : Fin 2) 1 m
  filter_upwards [parent_boundary_vector_swap_coeFn m u.toH1Function.gradToHilbertVectorL2,
    hmp.quasiMeasurePreserving.ae_eq_comp u.toH1Function.coeFn_gradToHilbertVectorL2,
    (u.swapOnOpenCubeSetOriginCube 0 1).toH1Function.coeFn_gradToHilbertVectorL2]
    with x hx hy hz
  change u.toH1Function.gradToHilbertVectorL2 (swapVecContinuousLinearEquiv (0 : Fin 2) 1 x) = _ at hy
  rw [hx,hy,hz]
  simp only [Function.comp_apply,hilbertifyVecField,HilbertVec.toVec_ofVec,
    H10Function.swapOnOpenCubeSetOriginCube_toH1Function,
    H1Function.swapOnOpenCubeSetOriginCube,swapVecContinuousLinearEquiv_apply]

/-- Every honest H10 gradient belongs to the exact closed projection range. -/
theorem parent_boundary_h10_gradient_mem (m : ℤ)
    (u : H10Function (openCubeSet (originCube 2 m))) :
    u.toH1Function.gradToHilbertVectorL2 ∈
      (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule := by
  refine ⟨⟨(u.toH1Function.toScalarL2,u.toH1Function.gradToHilbertVectorL2),
    (Submodule.le_topologicalClosure _)
      (h10_pair_mem_h10GraphSubmodule (U := openCubeSet (originCube 2 m)) u)⟩,?_⟩
  simp [H10GraphClosed.gradientCLM]

/-- The ACTUAL closed H10-gradient subspace is invariant under reflection. -/
theorem parent_boundary_gradient_range_flip (m : ℤ) (i : Fin 2)
    (F : HilbertVectorL2 (openCubeSet (originCube 2 m)))
    (hF : F ∈ (lambda8H10GradientRange
      (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule) :
    parentBoundaryVectorFlip m i F ∈ (lambda8H10GradientRange
      (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule := by
  obtain ⟨u,hu⟩ := lambda8DirichletProjection_isPotentialZeroTrace
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m)) F
  have hfix := ((lambda8H10GradientRange
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule.starProjection_eq_self_iff).mpr hF
  change lambda8DirichletProjection _ F=F at hfix
  rw [←hu.trans hfix,parent_boundary_h10_gradient_flip]
  exact parent_boundary_h10_gradient_mem m _

/-- The actual closed H10-gradient subspace is invariant under swap. -/
theorem parent_boundary_gradient_range_swap (m : ℤ)
    (F : HilbertVectorL2 (openCubeSet (originCube 2 m)))
    (hF : F ∈ (lambda8H10GradientRange
      (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule) :
    parentBoundaryVectorSwap m F ∈ (lambda8H10GradientRange
      (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule := by
  obtain ⟨u,hu⟩ := lambda8DirichletProjection_isPotentialZeroTrace
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m)) F
  have hfix := ((lambda8H10GradientRange
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule.starProjection_eq_self_iff).mpr hF
  change lambda8DirichletProjection _ F=F at hfix
  rw [←hu.trans hfix,parent_boundary_h10_gradient_swap]
  exact parent_boundary_h10_gradient_mem m _

/-- Reflection commutes with the genuine physical Dirichlet projection. -/
theorem parent_boundary_dirichlet_projection_flip (m : ℤ) (i : Fin 2)
    (F : HilbertVectorL2 (openCubeSet (originCube 2 m))) :
    parentBoundaryVectorFlip m i
      (lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m)) F) =
    lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))
      (parentBoundaryVectorFlip m i F) :=
  parent_boundary_projection_commutes _ _ (parent_boundary_vector_flip_involutive m i)
    (parent_boundary_gradient_range_flip m i) F

/-- Swap commutes with that same projection. -/
theorem parent_boundary_dirichlet_projection_swap (m : ℤ)
    (F : HilbertVectorL2 (openCubeSet (originCube 2 m))) :
    parentBoundaryVectorSwap m
      (lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m)) F) =
    lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))
      (parentBoundaryVectorSwap m F) :=
  parent_boundary_projection_commutes _ _ (parent_boundary_vector_swap_involutive m)
    (parent_boundary_gradient_range_swap m) F

end
end ASDExplicitGamma.Native
