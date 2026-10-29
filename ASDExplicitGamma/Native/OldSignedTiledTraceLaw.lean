module

public import ASDExplicitGamma.Native.OldSignedSourceCellTraceLaw

/-! The raw L2 profile for the complete common source tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Gaussian Cold Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- The same profile holds for the actual descendant average of any source
cell at an OLD refinement offset. No independence of its descendants is used. -/
theorem old_signed_tiled_trace_sequence_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l)
    (j : ℕ) :
    let Q := originCube 2 n
    eLpNorm (fun ω => rawWeakTraceSequence M n Q t ω (r+j)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) := by
  intro Q
  let I := SquareCells Q (r+j)
  let C := theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  let d : ℝ := (descendantsAtDepth Q (r+j)).card
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q (r+j))
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcell (U : I) : eLpNorm (rawCubeFourLoadTrace M n U.val t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    apply old_signed_source_cell_trace_L2 M h hM hg n r j hr t ht hstates U.val
    rw [scale_eq_sub_of_mem_descendantsAtDepth U.property]
    change n-((r+j:ℕ):ℤ)=n-(r:ℤ)-(j:ℤ)
    push_cast
    ring
  have hh := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure 2
    (by norm_num) (fun U : I => rawCubeFourLoadTrace M n U.val t)
    (fun _ => d⁻¹) (fun _ => C) (fun _ => inv_nonneg.mpr hd.le) (fun _ => hC) hcell
  have hcard : Fintype.card I=(descendantsAtDepth Q (r+j)).card := by simp [I,SquareCells]
  have hsum : (∑ _U : I,d⁻¹*C)=C := by
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
    change d*(d⁻¹*C)=C
    rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
  have he : (fun ω => rawWeakTraceSequence M n Q t ω (r+j))=
      (fun ω => ∑ U : I,d⁻¹*rawCubeFourLoadTrace M n U.val t ω) := by
    funext ω
    exact Finset.mul_sum _ _ _
  rw [he]
  rwa [hsum] at hh

end
end ASDExplicitGamma.Native
