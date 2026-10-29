module

public import ASDExplicitGamma.Native.OldSignedFlatBounds

/-! Centered OLD feedback bounds, with the affine contribution identically zero. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The centered pure second first weak estimate has no affine-history cost. -/
theorem old_signed_centered_pure_second_first_weak (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hmean : oldSignedBlockMean Q F = 0)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i))))
    (hfirst : (fun x => (F x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    let m := oldSignedBlockMean Q F
    let O := oldSignedBlockPositiveNorm Q (F - fun _ => m)
    let B := oldSignedInverseHistory Q a
    vectorWeakHaarNorm Q (fun x => (Z x).1) ≤
      (1 + Scalar.inverseHistoryDiscount) * B * O := by
  have hh := old_signed_flat_pure_second_first_weak Q nu sigma hnu hsigma k F hF hPfst hPsnd hfirst
  dsimp only at hh ⊢
  simpa only [hmean, blockVecDot, Prod.fst_zero, Prod.snd_zero, vecDot_zero_left, Real.sqrt_zero, mul_zero, zero_add] using hh

/-- The centered compatible first corrector estimate has no affine-history cost. -/
theorem old_signed_centered_compatible_first_corrector (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hmean : oldSignedBlockMean Q F = 0)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i))))
    (hcompat : ScalarCompatible (openCubeSet Q) F) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF)
    let m := oldSignedBlockMean Q F
    let O := oldSignedBlockPositiveNorm Q (F - fun _ => m)
    let B := oldSignedInverseHistory Q a
    let M := oldSignedResponseHistory Q a
    vectorWeakHaarNorm Q (fun x => (Z x).1 - (F x).1) ≤
      (Real.sqrt (B * M) + 1) * O := by
  have hh := old_signed_flat_compatible_first_corrector Q nu sigma hnu hsigma k F hF hPfst hPsnd hcompat
  dsimp only at hh ⊢
  simpa only [hmean, blockVecDot, Prod.fst_zero, Prod.snd_zero, vecDot_zero_left, Real.sqrt_zero, mul_zero, zero_add] using hh

end
end ASDExplicitGamma.Native
