module

public import ASDExplicitGamma.Native.OldSignedAveragePairing
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! Exact mixed OLD source pairing and its reciprocal-error remainder.
The flat reference term is kept for the signed covariance contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic
noncomputable section

/-- A pure-second source pairs with the actual reciprocal coefficient
flux, with no replacement of the weighted minimizer by an affine field. -/
theorem old_signed_energy_pure_second_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {A : Vec 2 → BlockVec 2} {g : Vec 2 → Vec 2}
    (hA : MemBlockL2 (openCubeSet Q) A) (hg : MemVectorL2 (openCubeSet Q) g) :
    oldSignedEnergyPairing Q nu sigma k A (fun x => (0,g x))=
      volumeAverage (openCubeSet Q) (fun x => vecDot
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (A x)).2 (g x)) := by
  have hG : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)) :=
    memBlockL2_blockField MemLp.zero hg
  unfold oldSignedEnergyPairing
  rw [←scalar_frame_bilinear_field Q nu sigma hnu hsigma k hG hA,
    (scalarFrameRealization Q nu sigma hnu hsigma k).energySymm,
    scalar_frame_bilinear_field Q nu sigma hnu hsigma k hA hG]
  simp only [blockVecDot,vecDot_zero_left,zero_add]
  congr 1
  funext x
  exact vecDot_comm _ _

/-- Subtracting the literal flat source leaves exactly its actual
reciprocal-flux error paired with the localized OLD source. -/
theorem old_signed_mixed_pairing_remainder (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {A F : Vec 2 → BlockVec 2} {g : Vec 2 → Vec 2}
    (hA : MemBlockL2 (openCubeSet Q) A) (hF : MemBlockL2 (openCubeSet Q) F)
    (hg : MemVectorL2 (openCubeSet Q) g) :
    oldSignedEnergyPairing Q nu sigma k A (fun x => (0,g x))-
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (g x))=
      volumeAverage (openCubeSet Q) (fun x => vecDot
        ((blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (A x)).2-(F x).2) (g x)) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hflux := memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 Q _ hEll hA)
  simp only [scalarCoefficientFlux] at hflux
  have hfs := memVectorL2_snd_of_memBlockL2 hF
  rw [old_signed_energy_pure_second_pairing Q nu sigma hnu hsigma k hA hg]
  rw [←volumeAverage_sub (integrableOn_vecDot_of_memVectorL2 hflux hg)
    (integrableOn_vecDot_of_memVectorL2 hfs hg)]
  congr 1
  funext x
  simp only [Pi.sub_apply,sub_eq_add_neg,vecDot_add_left,vecDot_neg_left]

/-- Constant-one local mixed-term estimate after retaining the literal
flat pairing. Every weak/positive norm is taken on this same actual cell. -/
theorem old_signed_mixed_pairing_remainder_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {A F : Vec 2 → BlockVec 2} {g : Vec 2 → Vec 2}
    (hA : MemBlockL2 (openCubeSet Q) A) (hF : MemBlockL2 (openCubeSet Q) F)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hs : ∀ i,Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g x i)))) :
    |oldSignedEnergyPairing Q nu sigma k A (fun x => (0,g x))-
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (g x))|≤
      vectorWeakHaarNorm Q (fun x =>
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (A x)).2-(F x).2)*
        vectorPositiveHaarNorm Q g := by
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hflux := memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 Q _ hEll hA)
  simp only [scalarCoefficientFlux] at hflux
  have hfs := memVectorL2_snd_of_memBlockL2 hF
  rw [old_signed_mixed_pairing_remainder Q nu sigma hnu hsigma k hA hF hg]
  exact old_signed_vector_average_pairing_bound Q _ g (hflux.sub hfs) hg hs

end
end ASDExplicitGamma.Native
