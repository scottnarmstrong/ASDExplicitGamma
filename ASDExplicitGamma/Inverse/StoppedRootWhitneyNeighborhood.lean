module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneySeparation
public import ASDExplicitGamma.Inverse.StoppedWhitneyNeighborhood

/-! A stopped lifted chain cannot have a closure-touching neighborhood two
macro-layers wide. All endpoint widths are paid before the contradiction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Connected fine ancestors at a successful separation cannot connect
touching endpoints in layers a and a+2. This is applied only to the stopped
two-layer chain, before any whole-component lift or finiteness assertion. -/
theorem root_stopped_chain_neighborhood_layer_le (M : ABKModel 2) (Q : TriadicCube 2)
    (H a : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η)
      (a+whitneyProfile H a) (rootBlockStart Q (a+whitneyProfile H a)))
    {U V A D B C : TriadicCube 2} (hA : A ∈ whitneyRootLayer Q H a)
    (htAU : CubeTouch A U) (htVD : CubeTouch V D)
    (hUB : RootWhitneyLift Q (a+whitneyProfile H a) U B)
    (hVC : RootWhitneyLift Q (a+whitneyProfile H a) V C)
    (hB : B.index ∈ fineOccupied (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η) ω)
    (hC : C.index ∈ fineOccupied (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η) ω)
    (hconn : (fineGraph.induce
      (fineOccupied (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η) ω)).Reachable
        ⟨B.index,hB⟩ ⟨C.index,hC⟩)
    (n : ℕ) (han : a ≤ n) (hD : D ∈ whitneyRootLayer Q H n) : n ≤ a+1 := by
  let base := a+whitneyProfile H a
  let side : ℝ := (3:ℝ)^(Q.scale-(base:ℤ))
  let clock : ℝ := (3:ℝ)^((base:ℝ)/4)
  have hbase : 333 ≤ base := by dsimp only [base,whitneyProfile]; omega
  have hd : ∀ d, (|C.index d-B.index d|:ℝ) ≤ clock := by
    intro d
    exact (successful_separation_fine_distance _ ω Q base hbase hgood
      hUB.1 rfl hconn d).le
  have hclock : 1 ≤ clock := by
    dsimp only [clock]
    exact Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 3) (by positivity)
  have hside : 0 ≤ side := (zpow_pos (by norm_num) _).le
  have hUV : ‖cubeCenter U-cubeCenter V‖ ≤ (clock+1)*side :=
    root_whitney_lift_center_distance hUB hVC clock (by linarith only [hclock]) hd
  have hBscale : B.scale = Q.scale-(base:ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hUB.1
  have hCscale : C.scale = Q.scale-(base:ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hVC.1
  have hUr : cubeRadius U ≤ side/2 := by
    obtain ⟨r,hr,hur⟩ := hUB.2
    simpa only [side,cubeRadius_eq_zpow_div_two,hBscale] using descendant_radius_le hur
  have hVr : cubeRadius V ≤ side/2 := by
    obtain ⟨r,hr,hvr⟩ := hVC.2
    simpa only [side,cubeRadius_eq_zpow_div_two,hCscale] using descendant_radius_le hvr
  have hAr : cubeRadius A ≤ side/2 := root_whitney_layer_radius_le Q H a a le_rfl hA
  have hDr : cubeRadius D ≤ side/2 := root_whitney_layer_radius_le Q H a n han hD
  have hAU : ‖cubeCenter A-cubeCenter U‖ ≤ side := by
    have hh := norm_cubeCenter_sub_le_of_cubeTouch htAU
    linarith only [hh,hAr,hUr]
  have hVD : ‖cubeCenter V-cubeCenter D‖ ≤ side := by
    have hh := norm_cubeCenter_sub_le_of_cubeTouch htVD
    linarith only [hh,hVr,hDr]
  have hAD : ‖cubeCenter A-cubeCenter D‖ ≤ 4*clock*side := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (cubeCenter A) (cubeCenter U) (cubeCenter D)
    have ht' := norm_sub_le_norm_sub_add_norm_sub (cubeCenter U) (cubeCenter V) (cubeCenter D)
    have hp := mul_nonneg (show 0 ≤ clock-1 by linarith only [hclock]) hside
    nlinarith only [ht,ht',hAU,hVD,hUV,hp]
  by_contra hn
  have hsep := root_whitney_layer_gap Q H a n (by omega : a+2 ≤ n) hA hD
  have hgate := whitney_separation_gate Q.scale H a (by omega)
  change 4*clock*side < (1/3:ℝ)*(3:ℝ)^(Q.scale-(a:ℤ)) at hgate
  have hp := (zpow_pos (by norm_num : (0:ℝ) < 3) (Q.scale-(a:ℤ))).le
  linarith only [hsep,hgate,hAD,hp]

end
end ASDExplicitGamma.Inverse
