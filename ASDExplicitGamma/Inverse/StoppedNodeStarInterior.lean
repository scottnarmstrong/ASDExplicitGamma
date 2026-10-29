module

public import ASDExplicitGamma.Inverse.StoppedComponentStarSupport

/-! A whole common-mesh star of an actual Whitney component node is strictly
inside the translated root. This supplies compact support for the literal
finite Kuhn interpolation without a boundary collar. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

/-- Refining below an actual source cell leaves its whole closed mesh star
strictly inside the root; the macro-layer margin pays the star radius. -/
theorem root_whitney_closed_star_interior (Q : TriadicCube 2) (H n J : ℕ)
    {V : TriadicCube 2} (hV : V ∈ whitneyRootLayer Q H n)
    (hJ : n+whitneyProfile H n ≤ J) {x y : Vec 2}
    (hy : y ∈ Metric.closedBall (cubeCenter V) (cubeRadius V))
    (hxy : ∀ k, |x k-y k| ≤ diagMeshRadius Q J) : x ∈ openCubeSet Q := by
  have hcenter : (3:ℝ)^(Q.scale-(n:ℤ)) <
      (3:ℝ)^Q.scale/2-‖cubeCenter V-triadicCubeShift Q‖ := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hV
    have hs := whitney_scale_le Q.scale H ⟨n,hP⟩
    rw [root_translate_cube_center Q P hs,add_sub_cancel_right]
    exact three_zpow_lt_boundaryMargin_cubeCenter_of_mem_whitneyLayer hP
  have hsV := root_whitney_layer_scale Q H n hV
  have hside : cubeScaleFactor V ≤ (3:ℝ)^(Q.scale-(n:ℤ))/3 := by
    have hp : 1 ≤ whitneyProfile H n := by unfold whitneyProfile; omega
    have hh := zpow_le_zpow_right₀ (a := (3:ℝ)) (by norm_num)
      (show Q.scale-(n:ℤ)-(whitneyProfile H n:ℤ) ≤ Q.scale-(n:ℤ)-1 by omega)
    change (3:ℝ)^V.scale ≤ _
    rw [hsV]
    apply hh.trans_eq
    rw [zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0),zpow_one]
  have hmesh : diagMeshRadius Q J ≤ cubeScaleFactor V := by
    rw [diag_mesh_radius_eq_zpow]
    change (3:ℝ)^(Q.scale-(J:ℤ)) ≤ (3:ℝ)^V.scale
    rw [hsV]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hxyN : ‖x-y‖ ≤ diagMeshRadius Q J := by
    apply (pi_norm_le_iff_of_nonneg (diagMeshRadius_pos Q J).le).mpr
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hxy
  have hyN := Metric.mem_closedBall.mp hy
  rw [dist_eq_norm,cubeRadius] at hyN
  have ht := norm_add_le (x-y) (y-cubeCenter V)
  have ht' := norm_add_le (x-cubeCenter V) (cubeCenter V-triadicCubeShift Q)
  rw [sub_add_sub_cancel] at ht ht'
  have hmacro : 0 ≤ (3:ℝ)^(Q.scale-(n:ℤ)) := (zpow_pos (by norm_num) _).le
  have hxN : ‖x-triadicCubeShift Q‖ < (3:ℝ)^Q.scale/2 := by
    linarith only [hcenter,hside,hmesh,hxyN,hyN,ht,ht',hmacro]
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,mem_translateSet_iff_sub_mem,
    mem_openCubeSet_originCube_iff]
  intro k
  have hcoord : |(x-triadicCubeShift Q) k| ≤ ‖x-triadicCubeShift Q‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x-triadicCubeShift Q) k
  have hk := hcoord.trans_lt hxN
  constructor <;> linarith only [abs_lt.mp hk]

end
end ASDExplicitGamma.Inverse
