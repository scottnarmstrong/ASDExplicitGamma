module

public import ASDExplicitGamma.Scalar.OldHessianTrialPatchWeak
public import ASDExplicitGamma.Scalar.OldHessianTrialSourceRegularity
public import ASDExplicitGamma.Scalar.OldHessianTrialConcreteTrial
public import ASDExplicitGamma.Native.OldSignedPureSecondSharp

/-! The actual complementary projection of the mixed source is paid by
its fine positive norm and the original complete fine inverse-history maximum. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian Variational Response
noncomputable section

/-- Pure-second projection control on the actual finite fine partition.
All coefficient restrictions and all complete-history factors are physical. -/
theorem old_hessian_pure_second_projected_energy (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (g : Vec 2 → Vec 2)
    (hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)))
    (hp : ∀ U∈descendantsAtDepth Q fine,∀ i : Fin 2,
      Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy U
        (cubeIncrement U (j+1) (fun x => g x i)))) :
    let R := oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun x => (0,g x)) hF
    oldSignedEnergyPairing Q nu sigma k R R ≤
      oldHessianFineInverseHistory Q fine nu sigma k*
        descendantsAverage Q fine (fun U => vectorPositiveHaarEnergy U g) := by
  intro R
  rw [old_signed_local_residual_cell_pairing]
  rw [←old_signed_cell_average_eq_descendantsAverage Q fine (fun U => vectorPositiveHaarEnergy U g),
    ←old_signed_cell_average_mul]
  apply old_signed_cell_average_mono
  intro U
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let hFU := hF.mono_measure (Measure.restrict_mono_set volume hsub)
  have hh := old_signed_pure_second_sharp_energy U.val nu sigma hnu hsigma kU g hFU (hp U.val U.property)
  rw [(old_signed_cell_histories Q U.val hsub nu sigma hnu hsigma k).1] at hh
  rw [vectorPositiveHaarNorm,Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U.val g)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (old_hessian_fine_history_le Q fine nu sigma k U.val U.property)
    (vectorPositiveHaarEnergy_nonneg U.val g))

/-- Representative-independent pure-second form, still keeping the exact
physical local residual in the conclusion. -/
theorem old_hessian_pure_second_field_projected_energy (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hzero : ∀ x,(F x).1=0)
    (hp : ∀ U∈descendantsAtDepth Q fine,∀ i : Fin 2,
      Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy U
        (cubeIncrement U (j+1) (fun x => (F x).2 i)))) :
    let R := oldSignedLocalResidual Q fine nu sigma hnu hsigma k F hF
    oldSignedEnergyPairing Q nu sigma k R R ≤
      oldHessianFineInverseHistory Q fine nu sigma k*
        descendantsAverage Q fine (fun U => vectorPositiveHaarEnergy U (fun x => (F x).2)) := by
  let g := fun x => (F x).2
  have he : F=(fun x => (0,g x)) := by
    funext x
    apply Prod.ext
    · exact hzero x
    · rfl
  have hG : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)) := by
    rw [←he]
    exact hF
  let Pack := {G : Vec 2 → BlockVec 2 // MemBlockL2 (openCubeSet Q) G}
  have hpack : (⟨F,hF⟩ : Pack)=⟨(fun x => (0,g x)),hG⟩ := Subtype.ext he
  have hr := congrArg (fun p : Pack => oldSignedLocalResidual Q fine nu sigma hnu hsigma k p.1 p.2) hpack
  intro R
  change oldSignedEnergyPairing Q nu sigma k
    (oldSignedLocalResidual Q fine nu sigma hnu hsigma k F hF)
    (oldSignedLocalResidual Q fine nu sigma hnu hsigma k F hF) ≤ _
  rw [hr]
  exact old_hessian_pure_second_projected_energy Q fine nu sigma hnu hsigma k g hG hp

/-- The actual coarse/fine mixed bottom source obeys the sharp fine-history
projection bound. Its Haar convergence and pure-block identity are proved
inside this theorem from the actual constructed potentials. -/
theorem old_hessian_actual_mixed_projection_energy (n : ℤ) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (b : ℝ) (L : {l : ℝ // 0<l}) (j : whiteBasisIndex) (i : Fin 2) :
    let Q := originCube 2 n
    let R := oldHessianMixedBottomResidual Q coarse fine nu sigma hnu hsigma k b L j i
    let F := oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L j i
    oldSignedEnergyPairing Q nu sigma k R R ≤
      oldHessianFineInverseHistory Q fine nu sigma k*
        descendantsAverage Q fine (fun U => vectorPositiveHaarEnergy U (fun x => (F x).2)) := by
  intro Q R F
  apply old_hessian_pure_second_field_projected_energy Q fine nu sigma hnu hsigma k F
    (old_hessian_mixed_bottom_source_memL2 Q coarse fine nu sigma hnu hsigma k b L j i)
  · intro x
    simp only [F,oldHessianMixedBottomSource,oldHessianMixedSource,
      oldSignedLocalizedPotentialShear,Prod.fst_add,zero_add]
  · intro U hU
    exact (old_hessian_mixed_source_positive n fine b L
      (oldSignedCanonicalFirstCorrector Q _
        (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
          nu sigma hnu hsigma k) (0,basisVec i))
      (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)) j U hU).1

end
end ASDExplicitGamma.Scalar
