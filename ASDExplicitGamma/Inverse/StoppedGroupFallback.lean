module

public import ASDExplicitGamma.Inverse.StoppedComponentFallback
public import ASDExplicitGamma.Inverse.StoppedGroupCorrection
public import ASDExplicitGamma.Inverse.StoppedMeshValueBounds
public import ASDExplicitGamma.Inverse.StoppedComponentStarSupport

/-! Uniform physical fallback bounds of the actual finite mesh groups.
Together with their two-layer support these establish summability before
the variational response estimate is invoked. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

/-- Exact common finer mesh is at least one ninth of its coarser parent side. -/
theorem whitney_common_mesh_parent_side_le (Q : TriadicCube 2) (H a : ℕ) :
    (3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) ≤
      9*diagMeshRadius Q (compatibleWhitneyMeshDepth H (a+1)) := by
  have hp := whitney_profile_step H a
  have he : Q.scale-((a+whitneyProfile H a:ℕ):ℤ) ≤
      Q.scale-(compatibleWhitneyMeshDepth H (a+1):ℤ)+2 := by
    unfold compatibleWhitneyMeshDepth
    omega
  have hh := zpow_le_zpow_right₀ (a := (3:ℝ)) (by norm_num) he
  rw [zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)] at hh
  rw [diag_mesh_radius_eq_zpow]
  norm_num only [zpow_ofNat,pow_two,mul_one] at hh
  simpa only [mul_comm] using hh

/-- The actual node range of every component in a common-mesh group has
the source deterministic physical stopped-diameter fallback. -/
theorem stopped_group_component_span_fallback (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (C : rootComponentGroup Q H S a)
    (hne : (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) :
    componentCoordinateMax Q _ (componentMeshNodes Q _ C.val) hne i-
      componentCoordinateMin Q _ (componentMeshNodes Q _ C.val) hne i ≤
      2*(3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)*(3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let base := a+whitneyProfile H a
  let clock : ℝ := (3:ℝ)^((base:ℝ)/4)
  let side : ℝ := (3:ℝ)^(Q.scale-(base:ℤ))
  obtain ⟨R,hR,he⟩ := C.property.1
  have ha : rootComponentLeastLayer Q H (badComponent S R)=a := by rw [← he]; exact C.property.2
  have hl : componentCoordinateMin Q J (componentMeshNodes Q J C.val) hne i ∈
      componentCoordinateSet Q J (componentMeshNodes Q J C.val) i := Finset.min'_mem _ _
  have hh : componentCoordinateMax Q J (componentMeshNodes Q J C.val) hne i ∈
      componentCoordinateSet Q J (componentMeshNodes Q J C.val) i := Finset.max'_mem _ _
  obtain ⟨zl,hzl,hel⟩ := Finset.mem_image.mp hl
  obtain ⟨zh,hzh,heh⟩ := Finset.mem_image.mp hh
  obtain ⟨U,hUC,hzu⟩ := (component_mesh_nodes_mem _ _ _ _).mp hzh
  obtain ⟨V,hVC,hzv⟩ := (component_mesh_nodes_mem _ _ _ _).mp hzl
  rw [he] at hUC hVC
  have hpair := stopped_component_closed_point_fallback M Q H hH τ η ω hgood S hS hbad R hR hUC hVC hzu hzv
  dsimp only at hpair
  rw [ha] at hpair
  change ‖diagInteriorVertex Q J zh-diagInteriorVertex Q J zl‖ ≤ (clock+1)*side at hpair
  have hcoord : diagInteriorVertex Q J zh i-diagInteriorVertex Q J zl i ≤
      ‖diagInteriorVertex Q J zh-diagInteriorVertex Q J zl‖ := by
    apply (le_abs_self _).trans
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (diagInteriorVertex Q J zh-diagInteriorVertex Q J zl) i
  have hs := hcoord.trans hpair
  rw [hel,heh] at hs
  have hc : 1 ≤ clock := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 3) (by positivity)
  have hside : 0 ≤ side := (zpow_pos (by norm_num) _).le
  have hprod := mul_nonneg (sub_nonneg.mpr hc) hside
  change _ ≤ 2*clock*side
  nlinarith only [hs,hprod]

/-- Every actual group nodal correction is bounded by one stopped physical
diameter payment, independently of the component count. -/
theorem stopped_group_nodal_fallback (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) (z : InteriorNode (compatibleWhitneyMeshDepth H (a+1))) :
    |rootGroupNodalCorrection Q H S a hfin hne i z| ≤
      (3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)*(3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) := by
  classical
  by_cases hz : ∃ C : rootComponentGroup Q H S a, z ∈ componentMeshNodes Q _ C.val
  · obtain ⟨C,hCz⟩ := hz
    rw [root_group_nodal_on_component Q H S a hfin hne C hCz i]
    apply (component_midpoint_displacement_bound Q _ _ (hne C) z hCz i).trans
    have hs := div_le_div_of_nonneg_right
      (stopped_group_component_span_fallback M Q H hH τ η ω hgood S hS hbad a C (hne C) i)
      (by norm_num : (0:ℝ) ≤ 2)
    convert hs using 1
    ring
  · rw [root_group_nodal_off_components Q H S a hfin hne i (fun C hC => hz ⟨C,hC⟩),abs_zero]
    positivity

/-- Global amplitude fallback for one actual group coordinate correction. -/
theorem stopped_group_correction_value_fallback (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) (x : Vec 2) :
    |(rootGroupCorrection Q H S a hfin hne i).toFun x| ≤
      (3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)*(3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) :=
  diag_synthesis_value_bound Q _ _ _ (by positivity)
    (stopped_group_nodal_fallback M Q H hH τ η ω hgood S hS hbad a hfin hne i) x

end
end ASDExplicitGamma.Inverse
