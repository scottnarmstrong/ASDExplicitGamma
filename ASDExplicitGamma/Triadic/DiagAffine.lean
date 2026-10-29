module

public import ASDExplicitGamma.Triadic.DiagInterpolant

/-! Exact affine recovery and source H¹₀ reduction of the DIAG operator. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

local instance diagAffineFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem diagMeanGradient_h10 (Q : TriadicCube 2) (u : H10Function (openCubeSet Q)) :
    diagMeanGradientLinear Q u.toH1Function = 0 := by
  funext i
  exact cubeAverage_h10_gradient_eq_zero Q u i

theorem diagResidualLinear_h10 (Q : TriadicCube 2) (u : H10Function (openCubeSet Q)) :
    diagResidualLinear Q u.toH1Function = u.toH1Function := by
  change u.toH1Function - diagAffineLinear Q (diagMeanGradientLinear Q u.toH1Function) = _
  rw [diagMeanGradient_h10, map_zero, sub_zero]

/-- The source H10 interpolant itself has zero trace. -/
theorem diagInterpolant_h10_memH10 (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    MemH10 (openCubeSet Q) (diagInterpolant Q j u.toH1Function).toFun := by
  change MemH10 _ ((diagAffineLinear Q (diagMeanGradientLinear Q u.toH1Function)) +
    diagSynthesisH1Linear Q j (diagNodalValuesLinear Q j u.toH1Function)).toFun
  rw [diagMeanGradient_h10, map_zero, zero_add]
  exact diagSynthesis_memH10 Q j _

theorem diagMeanGradient_affine (Q : TriadicCube 2) (p : Vec 2) :
    diagMeanGradientLinear Q (diagAffineLinear Q p) = p := by
  funext i
  change cubeAverage Q (fun _ => p i) = p i
  exact cubeAverage_const Q (p i)

/-- Every affine function is reproduced exactly as an H1 witness. -/
theorem diagInterpolant_affine (Q : TriadicCube 2) (j : ℕ) (p : Vec 2) :
    diagInterpolant Q j (diagAffineLinear Q p) = diagAffineLinear Q p := by
  have hz : diagResidualLinear Q (diagAffineLinear Q p) = 0 := by
    change diagAffineLinear Q p - diagAffineLinear Q (diagMeanGradientLinear Q (diagAffineLinear Q p)) = 0
    rw [diagMeanGradient_affine, sub_self]
  have hn : diagNodalValuesLinear Q j (diagAffineLinear Q p) = 0 := by
    funext z
    change diagOddNodalMeanLinear (cubeCorner Q) (diagMeshRadius Q j) (3^j)
      (diagInteriorVertexIndex j z)
      (diagProjectionLinear Q j (diagResidualLinear Q (diagAffineLinear Q p))) = 0
    rw [hz, map_zero, map_zero]
  change diagAffineLinear Q (diagMeanGradientLinear Q (diagAffineLinear Q p)) +
    diagSynthesisH1Linear Q j (diagNodalValuesLinear Q j (diagAffineLinear Q p)) = _
  rw [diagMeanGradient_affine, hn, map_zero, add_zero]

/-- The affine-data interpolant splits into its load and the actual H10 interpolant. -/
theorem diagInterpolant_affinePotential (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    diagInterpolant Q j (ASDExplicitGamma.Variational.lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) p u) =
        diagAffineLinear Q p + diagInterpolant Q j u.toH1Function := by
  change diagInterpolant Q j (diagAffineLinear Q p + u.toH1Function) = _
  rw [map_add, diagInterpolant_affine]

/-- The affine part cancels from the interpolation error exactly. -/
theorem diagInterpolant_affinePotential_residual (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    ASDExplicitGamma.Variational.lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) p u -
      diagInterpolant Q j (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p u) =
        u.toH1Function - diagInterpolant Q j u.toH1Function := by
  rw [diagInterpolant_affinePotential]
  change (diagAffineLinear Q p + u.toH1Function) -
    (diagAffineLinear Q p + diagInterpolant Q j u.toH1Function) = _
  abel

end

end ASDExplicitGamma.Triadic
