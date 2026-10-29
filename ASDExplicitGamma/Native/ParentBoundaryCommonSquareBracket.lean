module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterPhysical
public import ASDExplicitGamma.Gaussian.SquareLemmaV

/-! The common-center bracket on every translated triadic observation square. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Model Triadic Variational Response Gaussian Main
noncomputable section

/-- Complete common-center Lemma V bracket on any observation square. The
literal distance cap may use a center outside the observed child. -/
theorem parent_boundary_common_square_trace_bracket
    (Q : TriadicCube 2) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (H : ℕ → ResponseCoefficient (openCubeSet Q)) (η : ℕ → PlanarW2Infinity Q)
    (v L S : ℝ) (z : Vec 2) (hrep : RepresentsQ3Remainder η v L z)
    (hv : 0 ≤ v) (hL : 0 < L) (hS : 0 ≤ S)
    (hdist : ∀ x ∈ cubeSet Q,(x 0-z 0)^2+(x 1-z 1)^2 ≤ S^2/2)
    (hlink : ∀ l,(η l).value.toFun =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => responseCoefficientExtension (H l) x / σ) :
    let κ := Real.sqrt v*lemmaVH2Bn (S/L) (diagMeshRadius Q j/L)
    (∀ (s : Finset ℕ) (c : ℕ → ℝ),(∑ l ∈ s,c l^2) ≤ 1 →
      |fderiv ℝ (squareTrace Q ν σ) k (∑ l ∈ s,c l • H l)| ≤
        2*κ*lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)*
          Real.sqrt (squareTrace Q ν σ k*(squareTrace Q ν σ k+4))*Real.sqrt (∑ l ∈ s,c l^2)) ∧
    Summable (fun l => (fderiv ℝ (squareTrace Q ν σ) k (H l))^2) ∧
    (∑' l,(fderiv ℝ (squareTrace Q ν σ) k (H l))^2) ≤
      4*κ^2*(lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k))^2*
        squareTrace Q ν σ k*(squareTrace Q ν σ k+4) := by
  intro κ
  have hκ : 0 ≤ κ := by
    have hρ : 0 ≤ S/L := div_nonneg hS hL.le
    have hδ : 0 ≤ diagMeshRadius Q j/L := div_nonneg (diagMeshRadius_pos Q j).le hL.le
    dsimp [κ,lemmaVH2Bn,lemmaVH2C1,lemmaVH2C2]
    positivity
  exact square_lemmaV_of_interpolant Q j ν σ hν hσ k (diagInterpolant Q j)
    H (fun l => (η l).value) (fun l => (η l).value_memLp_top)
    (fun l b => (η l).gradient_memLp_top_volume b) hlink
    (fun p r => diagInterpolant_affine_residual_memH10 Q j p r) κ hκ
    (fun p u s c _ => parent_boundary_common_remainder_H2_distance
      Q j η v L S z hrep hv hL hS hdist p u s c)

end
end ASDExplicitGamma.Native
