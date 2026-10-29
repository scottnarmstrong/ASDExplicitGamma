module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneyLift
public import ASDExplicitGamma.Inverse.StoppedWhitneySeparation

/-! The exact physical diameter payment in the stopped two-layer argument. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- All layers at or below the first neighborhood layer have fine widths
bounded by that layer's actual mesh side. -/
theorem root_whitney_layer_radius_le (Q : TriadicCube 2) (H a n : ℕ) (han : a ≤ n)
    {V : TriadicCube 2} (hV : V ∈ whitneyRootLayer Q H n) :
    cubeRadius V ≤ (3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ))/2 := by
  rw [cubeRadius_eq_zpow_div_two,root_whitney_layer_scale Q H n hV]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 3)
  have hm := whitney_profile_mono H han
  omega

/-- Fine-lattice coordinate diameter gives the corresponding actual physical
center diameter, retaining the one total parent-width payment. -/
theorem root_whitney_lift_center_distance {Q : TriadicCube 2} {h : ℕ}
    {U V A B : TriadicCube 2} (hUA : RootWhitneyLift Q h U A)
    (hVB : RootWhitneyLift Q h V B) (t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ d, (|B.index d-A.index d|:ℝ) ≤ t) :
    ‖cubeCenter U-cubeCenter V‖ ≤ (t+1)*(3:ℝ)^(Q.scale-(h:ℤ)) := by
  have hAs : A.scale = Q.scale-h := scale_eq_sub_of_mem_descendantsAtDepth hUA.1
  have hBs : B.scale = Q.scale-h := scale_eq_sub_of_mem_descendantsAtDepth hVB.1
  have hside : 0 ≤ (3:ℝ)^(Q.scale-(h:ℤ)) := (zpow_pos (by norm_num) _).le
  have hU : ‖cubeCenter U-cubeCenter A‖ ≤ (3:ℝ)^(Q.scale-(h:ℤ))/2 := by
    obtain ⟨r,hr,hUr⟩ := hUA.2
    have hh := descendant_closed_cube_subset hUr (Metric.mem_closedBall_self (cubeRadius_nonneg U))
    rw [Metric.mem_closedBall,dist_eq_norm,cubeRadius_eq_zpow_div_two,hAs] at hh
    exact hh
  have hV : ‖cubeCenter B-cubeCenter V‖ ≤ (3:ℝ)^(Q.scale-(h:ℤ))/2 := by
    obtain ⟨r,hr,hVr⟩ := hVB.2
    have hh := descendant_closed_cube_subset hVr (Metric.mem_closedBall_self (cubeRadius_nonneg V))
    rw [Metric.mem_closedBall,dist_eq_norm,cubeRadius_eq_zpow_div_two,hBs,norm_sub_rev] at hh
    exact hh
  have hAB : ‖cubeCenter A-cubeCenter B‖ ≤ t*(3:ℝ)^(Q.scale-(h:ℤ)) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht hside)).mpr
    intro d
    change |cubeCenter A d-cubeCenter B d| ≤ _
    simp only [cubeCenter,cubeScaleFactor,hAs,hBs]
    rw [← sub_mul,abs_mul,abs_of_nonneg hside,abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd d) hside
  have htri := norm_sub_le_norm_sub_add_norm_sub (cubeCenter U) (cubeCenter A) (cubeCenter V)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (cubeCenter A) (cubeCenter B) (cubeCenter V)
  linarith only [hU,hV,hAB,htri,htri']

end
end ASDExplicitGamma.Inverse
