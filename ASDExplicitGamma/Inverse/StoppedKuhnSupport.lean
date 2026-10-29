module

public import ASDExplicitGamma.Inverse.StoppedKuhnNodalData
public import ASDExplicitGamma.Inverse.StoppedKuhnH1
public import ASDExplicitGamma.Inverse.StoppedNodeStarInterior

/-! Literal root Kuhn interpolation of source nodal values and its finite
closed-star support. The interpolation uses each group's own source mesh. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

def rootKuhnMesh (Q : TriadicCube 2) (j : ℕ) : Finset (KuhnCell 2) :=
  triadicSimplexPartition Q (Q.scale-(j:ℤ))

def kuhnNodalExtension (Q : TriadicCube 2) (j : ℕ) (b : InteriorNode j → ℝ) : Vec 2 → ℝ :=
  zeroExtendedKuhnAffine (rootKuhnMesh Q j) (diagSynthesisH1Linear Q j b).toFun

def nodalClosedStars (Q : TriadicCube 2) (j : ℕ) (b : InteriorNode j → ℝ) : Set (Vec 2) :=
  ⋃ z ∈ ({z | b z ≠ 0} : Set (InteriorNode j)),
    Metric.closedBall (diagInteriorVertex Q j z) (diagMeshRadius Q j)

theorem root_kuhn_mesh_scale (Q : TriadicCube 2) (j : ℕ)
    {T : KuhnCell 2} (hT : T ∈ rootKuhnMesh Q j) : T.supportCube.scale=Q.scale-(j:ℤ) :=
  supportCube_scale_eq_of_mem_triadicSimplexPartition (by omega) hT

theorem nodal_closed_stars_compact (Q : TriadicCube 2) (j : ℕ) (b : InteriorNode j → ℝ) :
    IsCompact (nodalClosedStars Q j b) :=
  (Set.toFinite _).isCompact_biUnion (fun _ _ => isCompact_closedBall _ _)

/-- A point in a closed simplex is within one side of each of its vertices. -/
theorem kuhn_closed_point_vertex_near (Q : TriadicCube 2) (j : ℕ)
    {T : KuhnCell 2} (hT : T ∈ rootKuhnMesh Q j) {x : Vec 2}
    (hx : x ∈ T.closedCarrier) (v : Fin 3) (i : Fin 2) :
    |x i-T.vertex v i| ≤ diagMeshRadius Q j := by
  have hxp := mem_closedBall_cubeCenter_iff.mp hx.1 i
  have hvp := mem_closedBall_cubeCenter_iff.mp (T.vertex_mem_closedCarrier v).1 i
  have hs : cubeScaleFactor T.supportCube=diagMeshRadius Q j := by
    change (3:ℝ)^T.supportCube.scale=diagMeshRadius Q j
    rw [root_kuhn_mesh_scale Q j hT,diag_mesh_radius_eq_zpow]
  rw [← hs]
  apply abs_le.mpr
  constructor <;> linarith only [hxp,hvp]

/-- The actual nodal Kuhn extension vanishes outside its finite closed stars.
No arbitrary support or continuity hypothesis enters this support theorem. -/
theorem kuhn_nodal_extension_zero_off_stars (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) {x : Vec 2} (hx : x ∉ nodalClosedStars Q j b) :
    kuhnNodalExtension Q j b x=0 := by
  classical
  by_cases ht : ∃ T ∈ rootKuhnMesh Q j, x ∈ T.closedCarrier
  · obtain ⟨T,hT,hxT⟩ := ht
    have hvert (v : Fin 3) : (diagSynthesisH1Linear Q j b).toFun (T.vertex v)=0 := by
      by_contra hv
      obtain ⟨z,hz,hbz⟩ := kuhn_nonzero_vertex_datum Q j b hT v hv
      apply hx
      refine Set.mem_iUnion₂.mpr ⟨z,(show b z ≠ 0 by rwa [hbz]),?_⟩
      rw [Metric.mem_closedBall,dist_eq_norm,hz]
      apply (pi_norm_le_iff_of_nonneg (diagMeshRadius_pos Q j).le).mpr
      intro i
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using kuhn_closed_point_vertex_near Q j hT hxT v i
    have hslope := kuhnSlope_eq_zero_of_vertex_const T (c := (0:ℝ)) hvert
    change zeroExtendedKuhnAffine _ _ x=0
    rw [zeroExtendedKuhnAffine_of_mem_closedCarrier (fun U hU => root_kuhn_mesh_scale Q j hU) _ hT hxT,
      kuhnInterp_apply,hvert 0,hslope]
    simp only [vecDot_zero_left,zero_add]
  · exact zeroExtendedKuhnAffine_of_forall_notMem _ _ (by simpa only [not_exists,not_and] using ht)

end
end ASDExplicitGamma.Inverse
