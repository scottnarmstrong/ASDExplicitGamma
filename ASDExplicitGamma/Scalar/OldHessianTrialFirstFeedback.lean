module

public import ASDExplicitGamma.Scalar.OldHessianTrialProjectedSource

/-! The fine pure-source first-potential feedback retains D_f=1.26 for the
actual mixed source. Its zero-trace fine potentials are constructed internally. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian Variational Response
noncomputable section

/-- The sharp rounded first-potential bound, using the proved 1/2+alpha
forced-source estimate instead of its older 1+alpha weakening. -/
theorem old_hessian_pure_second_first_feedback (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (g : Vec 2 → Vec 2)
    (hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)))
    (hp : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g x i)))) (v : H10Function (openCubeSet Q))
    (hv : (fun x => (scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad) :
    vectorWeakHaarNorm Q v.toH1Function.grad ≤
      (63/50:ℝ)*oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k)*
        vectorPositiveHaarNorm Q g := by
  have hg : MemLp g 2 (normalizedCubeMeasure Q) := memLp_pi_iff.mpr
    (fun i => memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
  have hv' : (fun x => (projectedSourceField Q nu sigma hnu hsigma k hg x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad := by
    unfold projectedSourceField
    rw [old_signed_pure_second_load_eq Q g hg hF]
    exact hv
  simpa only [vectorWeakHaarNorm,vectorPositiveHaarNorm,oldSignedInverseHistory,
    show (126/100:ℝ)=63/50 by norm_num] using
      projectedSource_forced_feedback_bound_le_126 Q nu sigma hnu hsigma k hg hp v hv'

/-- The genuine fine cell first corrector of a pure-second physical input
has the sharp feedback constant and the original physical inverse history. -/
theorem old_hessian_cell_first_feedback (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hzero : ∀ x,(F x).1=0)
    (hp : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => (F x).2 i)))) :
    vectorWeakHaarNorm U
      (oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k F hF).toH1Function.grad ≤
      (63/50:ℝ)*oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma k)*
        vectorPositiveHaarNorm U (fun x => (F x).2) := by
  let v := oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k F hF
  let g := fun x => (F x).2
  have he : F=(fun x => (0,g x)) := by
    funext x
    exact Prod.ext (hzero x) rfl
  have hG : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)) := by
    rw [←he]
    exact hF
  let Pack := {G : Vec 2 → BlockVec 2 // MemBlockL2 (openCubeSet Q) G}
  have hpack : (⟨F,hF⟩ : Pack)=⟨(fun x => (0,g x)),hG⟩ := Subtype.ext he
  have hres := congrArg (fun p : Pack => oldSignedCellResidual Q U hU nu sigma hnu hsigma k p.1 p.2) hpack
  let kU := oldSignedCellCoefficient Q U hU k
  let hGU := hG.mono_measure (Measure.restrict_mono_set volume hU)
  have hv : (fun x => (scalarResidualField U nu sigma hnu hsigma kU
      (toHilbertBlockL2OfBlockField hGU) x).1) =ᵐ[volumeMeasureOn (openCubeSet U)] v.toH1Function.grad := by
    apply Filter.Eventually.of_forall
    intro x
    rw [old_signed_cell_first_corrector_grad]
    dsimp only
    rw [hzero x,sub_zero]
    rw [hres]
    rfl
  have hh := old_hessian_pure_second_first_feedback U nu sigma hnu hsigma kU g hGU hp v hv
  rw [(old_signed_cell_histories Q U hU nu sigma hnu hsigma k).1] at hh
  exact hh

/-- The actual mixed bottom source retains the original fine derivative
feedback. All pure-source and complete-Haar facts are discharged internally. -/
theorem old_hessian_actual_mixed_first_feedback (n : ℤ) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (b : ℝ) (L : {l : ℝ // 0<l}) (j : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) fine) :
    let Q := originCube 2 n
    let F := oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L j i
    let hF := old_hessian_mixed_bottom_source_memL2 Q coarse fine nu sigma hnu hsigma k b L j i
    vectorWeakHaarNorm U
      (oldSignedCellFirstCorrector Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU)
        nu sigma hnu hsigma k F hF).toH1Function.grad ≤
      (63/50:ℝ)*oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma k)*
        vectorPositiveHaarNorm U (fun x => (F x).2) := by
  intro Q F hF
  apply old_hessian_cell_first_feedback Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    nu sigma hnu hsigma k F hF
  · intro x
    simp only [F,oldHessianMixedBottomSource,oldHessianMixedSource,
      oldSignedLocalizedPotentialShear,Prod.fst_add,zero_add]
  · exact (old_hessian_mixed_source_positive n fine b L
      (oldSignedCanonicalFirstCorrector Q _
        (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
          nu sigma hnu hsigma k) (0,basisVec i))
      (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)) j U hU).1

end
end ASDExplicitGamma.Scalar
