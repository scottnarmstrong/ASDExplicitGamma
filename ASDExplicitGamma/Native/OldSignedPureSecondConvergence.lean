module

public import ASDExplicitGamma.Native.OldSignedFirstWeakEnergy
public import ASDExplicitGamma.Native.OldSignedResidualEnergyContraction
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Qualitative convergence bounds for first potentials of the actual
pure-second weighted residuals. Sharp history constants are not used here. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- The first weak norm of the actual pure-second residual is bounded by
a finite physical constant times its positive source norm. This bound is
used for convergence only, not for the sharper AN error coefficient. -/
theorem old_signed_pure_second_residual_first_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (g : Vec 2 → Vec 2) (hg : MemVectorL2 (openCubeSet Q) g)
    (hs : ∀ i,Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g x i)))) :
    let S := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField (show MemBlockL2 (openCubeSet Q) (fun x => (0,g x)) from
        memBlockL2_blockField MemLp.zero hg))
    vectorWeakHaarNorm Q (fun x => (S x).1)^2≤(sigma/nu)^2*vectorPositiveHaarNorm Q g^2 := by
  intro S
  have hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)) := memBlockL2_blockField MemLp.zero hg
  have hS : MemBlockL2 (openCubeSet Q) S := S.property
  have hfirst := old_signed_first_weak_le_energy Q nu sigma hnu hsigma k S hS
  have hcontract := old_signed_residual_field_energy_contraction Q nu sigma hnu hsigma k _ hF
  change oldSignedEnergyPairing Q nu sigma k S S≤oldSignedEnergyPairing Q nu sigma k (fun x => (0,g x)) (fun x => (0,g x)) at hcontract
  rw [old_signed_pure_second_input_energy Q nu sigma hnu hsigma k g] at hcontract
  have hpos := vectorL2_le_vectorPositiveHaar Q g
    (fun i => memLp_normalized_of_memL2On (hg.eval i)) hs
  have hL2 : (∑ i : Fin 2,energy Q (fun x => g x i))≤vectorPositiveHaarNorm Q g^2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hpos 2
    simpa only [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => energy_nonneg Q _))] using hh
  have havg := old_signed_vector_average_pairing Q g g hg hg
  change volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x))=
    ∑ i : Fin 2,energy Q (fun x => g x i) at havg
  rw [←havg] at hL2
  calc
    _ ≤ (sigma/nu)*((sigma/nu)*volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x))) :=
      hfirst.trans (mul_le_mul_of_nonneg_left hcontract (div_nonneg hsigma.le hnu.le))
    _ = (sigma/nu)^2*volumeAverage (openCubeSet Q) (fun x => vecNormSq (g x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)

/-- A summable source-norm square series gives actual square-summability
of the first weak norms of the constructed weighted residuals. -/
theorem old_signed_pure_second_residual_first_summable {I : Type*} (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (g : I → Vec 2 → Vec 2) (hg : ∀ n,MemVectorL2 (openCubeSet Q) (g n))
    (hp : ∀ n i,Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g n x i))))
    (hs : Summable (fun n => vectorPositiveHaarNorm Q (g n)^2)) :
    Summable (fun n => vectorWeakHaarNorm Q (fun x =>
      (scalarResidualField Q nu sigma hnu hsigma k
        (toHilbertBlockL2OfBlockField (show MemBlockL2 (openCubeSet Q) (fun x => (0,g n x)) from
          memBlockL2_blockField MemLp.zero (hg n))) x).1)^2) := by
  apply (hs.mul_left ((sigma/nu)^2)).of_nonneg_of_le (fun n => sq_nonneg _)
  intro n
  exact old_signed_pure_second_residual_first_bound Q nu sigma hnu hsigma k (g n) (hg n) (hp n)

end
end ASDExplicitGamma.Native
