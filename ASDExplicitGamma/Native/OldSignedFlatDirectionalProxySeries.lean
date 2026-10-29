module

public import ASDExplicitGamma.Native.OldSignedPureSecondPairing
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedAffineContribution

/-! Convergence of all actual plus-source directional affine proxies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Triadic
noncomputable section

/-- The complete covariance-mode sum of the actual directional proxies is
summable, before it is used in any feedback norm. -/
theorem old_signed_actual_plus_directional_proxy_series (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField nu sigma kU) (m n i).2) := by
  intro kU m
  let p := fun n i => oldSignedDirectionalProxy U
    (responseFramePlanarCoefficientField nu sigma kU) (m n i).2
  have hp0 (n : whiteBasisIndex) (i : Fin 2) : 0≤p n i :=
    (old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma kU (m n i).2).1
  let H := Inverse.rawWeakTraceProxy
    (Variational.lemmaVInverseDepthMax U (responseFramePlanarCoefficientField nu sigma kU))
    (fun j => descendantsAverage U j (fun V => traceDefect (openCubeSet V)
      (responseFramePlanarCoefficientField nu sigma kU) 1))
  have hmeanNorm (n : whiteBasisIndex) (i : Fin 2) :
      vecNormSq (m n i).2=blockVecDot (m n i) (m n i) := by
    simp [m,oldSignedBlockMean,oldSignedFlatPlusBlock,
      cubeAverage_const,blockVecDot,vecDot,vecNormSq]
  have hs := (old_signed_flat_mean_budget_series Q depth b L true U hU).mul_left H
  apply Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun i _ => hp0 n i)) _ hs
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := (old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma kU (m n i).2).2
  rwa [hmeanNorm] at hh

end
end ASDExplicitGamma.Native
