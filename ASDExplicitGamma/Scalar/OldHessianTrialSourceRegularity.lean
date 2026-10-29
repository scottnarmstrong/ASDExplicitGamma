module

public import ASDExplicitGamma.Scalar.OldHessianTrialColumnSource
public import ASDExplicitGamma.Scalar.OldHessianTrialRowSource
public import ASDExplicitGamma.Scalar.OldHessianTrialMixedSource
public import ASDExplicitGamma.Triadic.VectorPositiveMultiplier

/-! Genuine complete fine-cell positive regularity of the mixed source.
The exact row-plus-product triangle is proved for the physical fields. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian Variational
noncomputable section

/-- The actual mixed source has all its fine positive-Haar series and the
literal row/product norm triangle, with no regularity estimate premise. -/
theorem old_hessian_mixed_source_positive (n : ℤ) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v phi : H10Function (openCubeSet (originCube 2 n)))
    (j : whiteBasisIndex) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) fine) :
    let Q := originCube 2 n
    let eta := (mainQ3DirectionW2 Q b L (whiteBasis j)).value
    let F := oldHessianMixedSource (diagInterpolant Q fine) eta v.toH1Function phi.toH1Function
    (∀ i : Fin 2,Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => (F x).2 i)))) ∧
    vectorPositiveHaarNorm U (fun x => (F x).2) ≤
      vectorPositiveHaarNorm U (fun x =>
        (oldSignedLocalizedPotentialShear (diagInterpolant Q fine) eta
          (v.toH1Function-phi.toH1Function) x).2)+
      vectorPositiveHaarNorm U (oldHessianCoarseProduct Q b L phi (whiteBasis j)) := by
  intro Q eta F
  let R := fun x => (oldSignedLocalizedPotentialShear (diagInterpolant Q fine)
    eta (v.toH1Function-phi.toH1Function) x).2
  let G := fun x => -(oldHessianCoarseProduct Q b L phi (whiteBasis j) x)
  have hRm : ∀ i : Fin 2,MemLp (fun x => R x i) 2 (normalizedCubeMeasure U) := by
    intro i
    have hp := old_signed_localized_potential_shear_memL2 Q (diagInterpolant Q fine)
      eta (v.toH1Function-phi.toH1Function)
      (mainQ3DirectionW2 Q b L (whiteBasis j)).value_memLp_top
      (mainQ3DirectionW2 Q b L (whiteBasis j)).gradient_memLp_top_volume
    have hlocal := hp.mono_measure
      (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hlocal) i)
  have hRp (i : Fin 2) : Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => R x i))) :=
    old_hessian_localized_row_positive n fine b L (v-phi) U hU j i
  have hGm (i : Fin 2) : MemLp (fun x => G x i) 2 (normalizedCubeMeasure U) :=
    (old_hessian_coarse_product_regular Q fine b L phi j U hU i).1.neg
  have hGp (i : Fin 2) : Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => G x i))) := by
    change Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U (cubeIncrement U (k+1)
      (fun x => -oldHessianCoarseProduct Q b L phi (whiteBasis j) x i)))
    simp_rw [cubeIncrement_neg,energy_neg]
    exact (old_hessian_coarse_product_regular Q fine b L phi j U hU i).2
  have he : (fun x => (F x).2)=(fun x i => R x i+G x i) := rfl
  have hnorm : vectorPositiveHaarNorm U G =
      vectorPositiveHaarNorm U (oldHessianCoarseProduct Q b L phi (whiteBasis j)) := by
    unfold G vectorPositiveHaarNorm vectorPositiveHaarEnergy
    simp only [Pi.neg_apply,primalEnergy_neg]
  have hh := vectorPositiveHaar_add_le U R G hRm hGm hRp hGp
  rw [hnorm] at hh
  rw [he]
  exact hh

end
end ASDExplicitGamma.Scalar
