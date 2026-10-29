module

public import ASDExplicitGamma.Native.OldSignedDualReflection
public import ASDExplicitGamma.Native.OldSignedFlatProjection

/-! Weighted projection orthogonality gives compatible reflected residuals. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The reflected residual is compatible for every source class. Both
components follow from the actual projection Euler equation. -/
theorem old_signed_reflected_residual_compatible (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (H : HilbertBlockL2 (openCubeSet Q)) :
    ScalarCompatible (openCubeSet Q) (oldSignedDualReflection Q nu sigma k
      (scalarResidualField Q nu sigma hnu hsigma k H)) := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let Z := scalarResidualField Q nu sigma hnu hsigma k H
  let J := scalarCoefficientFlux a Z
  have hJ : MemBlockL2 U J := scalar_coefficient_flux_memL2 Q a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) (Lp.memLp Z)
  have hv : (volume U).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have havg (f : Vec 2 → ℝ) (hf : volumeAverage U f=0) : ∫ x in U,f x=0 := by
    change (volume U).toReal⁻¹*(∫ x in U,f x)=0 at hf
    exact (mul_eq_zero.mp hf).resolve_left (inv_ne_zero hv)
  have hzeroP : IsPotentialZeroTraceOn U (fun _ : Vec 2 => (0 : Vec 2)) :=
    ⟨0,rfl⟩
  have hzeroS : IsSolenoidalZeroNormalTraceOn U (fun _ : Vec 2 => (0 : Vec 2)) := by
    intro phi
    simp only [vecDot_zero_left,integral_zero]
  refine ⟨old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (Lp.memLp Z),?_,?_⟩
  · let oldSignedResidualDualFinite : IsFiniteMeasure (volumeMeasureOn U) :=
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
    apply IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_openCubeSet Q)) (memVectorL2_snd_of_memBlockL2 hJ)
    intro g hg hsol
    have hh := scalar_residual_field_orthogonal Q nu sigma hnu hsigma k H
      (fun x => (0,g x)) ⟨memBlockL2_blockField (memVectorL2_const 0) hg,hzeroP,hsol⟩
    apply havg
    simpa only [J,Z,a,U,scalarCoefficientFlux,blockVecDot,vecDot_zero_left,zero_add] using hh
  · intro phi
    have hh := scalar_residual_field_orthogonal Q nu sigma hnu hsigma k H
      (fun x => (phi.toH1Function.grad x,0))
      ⟨memBlockL2_blockField phi.toH1Function.grad_memVectorL2 (memVectorL2_const 0),
        phi.isPotentialZeroTraceOn,hzeroS⟩
    have hh' := havg _ hh
    simpa only [U,oldSignedDualReflection,Prod.snd_swap,blockVecDot,vecDot_zero_left,add_zero,vecDot_comm] using hh'

end
end ASDExplicitGamma.Native
