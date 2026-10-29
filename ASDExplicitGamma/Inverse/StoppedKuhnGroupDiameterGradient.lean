module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupFields
public import ASDExplicitGamma.Inverse.StoppedGroupNodalDiameter

/-! Exact physical current-ancestor Z charge on the literal Kuhn midpoint
group, with the same source coordinate constant 18. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

theorem stopped_kuhn_group_gradient_diameter_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i k : Fin 2) (n : ℕ) (P T : TriadicCube 2)
    (hP : P ∈ whitneyRootLayer Q H n)
    (hPT : RootWhitneyLift Q (a+whitneyProfile H a) P T)
    (hfinite : diameterField (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a)) τ η)
      ω (fineBlockIndex T.index) ≠ ∞)
    (x : Vec 2) (hx : x ∈ openCubeSet P)
    (U : KuhnCell 2) (hU : U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)))
    (hxU : x ∈ U.openCarrier) :
    |(rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k| ≤
      18*(3:ℝ)^40*realDiameterField
        (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a)) τ η) (fineBlockIndex T.index) ω := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let base := a+whitneyProfile H a
  let side : ℝ := (3:ℝ)^(Q.scale-(base:ℤ))
  let Z := realDiameterField (q3PlanarMarks M (Q.scale-base) τ η) (fineBlockIndex T.index) ω
  let b := rootGroupNodalCorrection Q H S a hfin hne i
  have hZ : 0 ≤ Z := ENNReal.toReal_nonneg
  have hside : 0 ≤ side := (zpow_pos (by norm_num) _).le
  have hc : 0 ≤ (3:ℝ)^40 := by norm_num
  have hpayment : 0 ≤ (3:ℝ)^40*Z*side := mul_nonneg (mul_nonneg hc hZ) hside
  have hb (v : Fin 3) : |(rootGroupCorrection Q H S a hfin hne i).toFun (U.vertex v)| ≤ (3:ℝ)^40*Z*side := by
    by_cases hv : (rootGroupCorrection Q H S a hfin hne i).toFun (U.vertex v)=0
    · rw [hv,abs_zero]
      exact hpayment
    have hv' : (diagSynthesisH1Linear Q J b).toFun (U.vertex v) ≠ 0 := hv
    obtain ⟨z,hz,hbz⟩ := kuhn_nonzero_vertex_datum Q J b hU v hv'
    have hz0 : b z ≠ 0 := by rwa [hbz]
    have hn (d : Fin 2) : |x d-diagInteriorVertex Q J z d| ≤ diagMeshRadius Q J := by
      rw [hz]
      exact kuhn_closed_point_vertex_near Q J hU (U.openCarrier_subset_closedCarrier hxU) v d
    have hh := stopped_group_node_diameter_bound M Q H hH τ η ω hgood S hS hbad a hfin hne i n P T hP hPT hfinite x hx z hz0 hn
    change |b z| ≤ (3:ℝ)^40*Z*side at hh
    rw [hbz] at hh
    exact hh
  rw [root_kuhn_group_gradient_on_simplex M Q H hH τ η ω hgood S hS hbad a hfin hne i k hU hxU]
  have hh := kuhn_slope_abs_bound U (rootGroupCorrection Q H S a hfin hne i).toFun ((3:ℝ)^40*Z*side) hb k
  have hs : cubeScaleFactor U.supportCube=diagMeshRadius Q J := by
    change (3:ℝ)^U.supportCube.scale=diagMeshRadius Q J
    rw [root_kuhn_mesh_scale Q J hU,diag_mesh_radius_eq_zpow]
  rw [hs] at hh
  apply hh.trans
  apply (div_le_iff₀ (diagMeshRadius_pos Q J)).mpr
  have hm := mul_le_mul_of_nonneg_left (whitney_common_mesh_parent_side_le Q H a)
    (show 0 ≤ 2*(3:ℝ)^40*Z from mul_nonneg (mul_nonneg (by norm_num) hc) hZ)
  change 2*((3:ℝ)^40*Z*side) ≤ 18*(3:ℝ)^40*Z*diagMeshRadius Q J
  nlinarith only [hm]

end
end ASDExplicitGamma.Inverse
