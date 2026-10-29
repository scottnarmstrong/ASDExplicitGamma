module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneySeparation

/-! Whole closed-cell points, rather than only cell centers, obey the
physical diameter payment of their common-mesh ancestors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Two closed parent-cube points cost one total fine side beyond the
ancestor coordinate span. -/
theorem equal_scale_closed_point_distance (A B : TriadicCube 2) (j : ℤ)
    (hA : A.scale=j) (hB : B.scale=j) {p q : Vec 2}
    (hp : p ∈ Metric.closedBall (cubeCenter A) (cubeRadius A))
    (hq : q ∈ Metric.closedBall (cubeCenter B) (cubeRadius B))
    (t : ℝ) (ht : 0 ≤ t) (hd : ∀ d, (|B.index d-A.index d|:ℝ) ≤ t) :
    ‖p-q‖ ≤ (t+1)*(3:ℝ)^j := by
  have hside : 0 ≤ (3:ℝ)^j := (zpow_pos (by norm_num) _).le
  have hp' : ‖p-cubeCenter A‖ ≤ (3:ℝ)^j/2 := by
    rw [Metric.mem_closedBall,dist_eq_norm,cubeRadius_eq_zpow_div_two,hA] at hp
    exact hp
  have hq' : ‖cubeCenter B-q‖ ≤ (3:ℝ)^j/2 := by
    rw [Metric.mem_closedBall,dist_eq_norm,cubeRadius_eq_zpow_div_two,hB,norm_sub_rev] at hq
    exact hq
  have hAB : ‖cubeCenter A-cubeCenter B‖ ≤ t*(3:ℝ)^j := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht hside)).mpr
    intro d
    change |cubeCenter A d-cubeCenter B d| ≤ _
    simp only [cubeCenter,cubeScaleFactor,hA,hB]
    rw [← sub_mul,abs_mul,abs_of_nonneg hside,abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd d) hside
  have ht1 := norm_sub_le_norm_sub_add_norm_sub p (cubeCenter A) q
  have ht2 := norm_sub_le_norm_sub_add_norm_sub (cubeCenter A) (cubeCenter B) q
  linarith only [hp',hq',hAB,ht1,ht2]

/-- The same exact payment applies to arbitrary points of actual lifted
Whitney cells, including all their closed faces and vertices. -/
theorem root_lift_closed_point_distance {Q : TriadicCube 2} {h : ℕ}
    {U V A B : TriadicCube 2} (hUA : RootWhitneyLift Q h U A)
    (hVB : RootWhitneyLift Q h V B) {p q : Vec 2}
    (hp : p ∈ Metric.closedBall (cubeCenter U) (cubeRadius U))
    (hq : q ∈ Metric.closedBall (cubeCenter V) (cubeRadius V))
    (t : ℝ) (ht : 0 ≤ t) (hd : ∀ d, (|B.index d-A.index d|:ℝ) ≤ t) :
    ‖p-q‖ ≤ (t+1)*(3:ℝ)^(Q.scale-(h:ℤ)) := by
  obtain ⟨r,hr,hU⟩ := hUA.2
  obtain ⟨s,hs,hV⟩ := hVB.2
  exact equal_scale_closed_point_distance A B _
    (scale_eq_sub_of_mem_descendantsAtDepth hUA.1) (scale_eq_sub_of_mem_descendantsAtDepth hVB.1)
    (descendant_closed_cube_subset hU hp) (descendant_closed_cube_subset hV hq) t ht hd

end
end ASDExplicitGamma.Inverse
