module

public import ASDExplicitGamma.Inverse.RawHistoryReal
public import Homogenization.Besov.Poincare.Projection
public import ASDExplicitGamma.Inverse.ContainedTriangleRootDepth
public import ASDExplicitGamma.Inverse.ContainedTriangleHistory

/-! The actual contained-triangle history budget, with all physical
weights and the exact protected old label retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
noncomputable section

/-- Summability of the exact first-depth majorant, before any response
comparison. This uses the raw history rather than its square-root moment. -/
theorem triangle_history_majorant_summable (D : ℕ → ℝ) (hD : ∀ r, 0 ≤ D r)
    (hs : Summable (fun r : ℕ => (3:ℝ)^(-(r:ℝ)/2)*D r)) (a : ℕ) (ha : a ≤ 2) :
    Summable (fun n : ℕ => 2*(1/3:ℝ)^(n+1)*D (a+n+1)) := by
  have hi : Function.Injective (fun n : ℕ => a+n+1) := by
    intro n m hh
    change a+n+1=a+m+1 at hh
    omega
  have hc := (hs.comp_injective hi).mul_left (2*Real.sqrt 3)
  apply hc.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hD _))
  intro n
  simpa only [Function.comp_apply,mul_assoc] using mul_le_mul_of_nonneg_right (triangle_history_weight a n ha) (hD _)

/-- The full actual weighted defect sum in a depth-at-most-two simplex has
the sharper bound 2 sqrt(3) tau. All descendant bounds and summability are
derived from the actual good root history in the same completed-label frame. -/
theorem triangle_good_parent_history_budget (M : ABKModel 2) (n : ℤ)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∈ clippedCellGoodEvent M n Q τ) :
    let B := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
      ((volume (openCubeSet (rootTranslateCube U P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
          historyOperatorDefect M n (rootTranslateCube U P) ω
    Summable B ∧ (∑' i, B i) ≤ 2*Real.sqrt 3*τ := by
  classical
  let D := fun r => rawDefectDepthMax M n Q r ω
  have hD (r) : 0 ≤ D r := ENNReal.toReal_nonneg
  have hraw := good_raw_history_real_series M n Q τ hτ ω hgood
  have he (r : ℕ) : (3:ℝ)^(-(r:ℝ)/2)*D r=(3:ℝ)^(-(1/2:ℝ)*r)*D r := by
    congr 2
    ring
  have hs : Summable (fun r : ℕ => (3:ℝ)^(-(r:ℝ)/2)*D r) := by simpa only [he] using hraw.1
  have hb : (∑' r : ℕ, (3:ℝ)^(-(r:ℝ)/2)*D r) ≤ τ := by simpa only [he] using hraw.2
  have hmaj := triangle_history_majorant_summable D hD hs a ha
  dsimp only
  let B := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
    ((volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
        historyOperatorDefect M n (rootTranslateCube U P) ω
  have hB0 (i : ℕ) : 0 ≤ B i := by
    apply Finset.sum_nonneg
    intro P _
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (norm_nonneg _)
  have hB (i : ℕ) : B i ≤ 2*(1/3:ℝ)^(i+1)*D (a+i+1) := by
    calc
      B i ≤ ∑ P ∈ triangleFirstCubes U.scale pi i,
        ((volume (openCubeSet (rootTranslateCube U P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*D (a+i+1) := by
        apply Finset.sum_le_sum
        intro P hP
        apply mul_le_mul_of_nonneg_left _ (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        have hd := mem_descendantsAtDepth_add hU (triangle_first_root_descendant U pi i hP)
        have hdd : a+(i+1)=a+i+1 := by omega
        rw [hdd] at hd
        exact operator_defect_le_depth_max M n Q (a+i+1) ω hd
      _ = _ := by rw [← Finset.sum_mul,triangle_root_first_weights]
  have hBs := hmaj.of_nonneg_of_le hB0 hB
  refine ⟨hBs,?_⟩
  exact (hBs.tsum_le_tsum hB hmaj).trans ((triangle_raw_history_bound D hD hs a ha).trans
    (mul_le_mul_of_nonneg_left hb (by positivity)))

end
end ASDExplicitGamma.Inverse
