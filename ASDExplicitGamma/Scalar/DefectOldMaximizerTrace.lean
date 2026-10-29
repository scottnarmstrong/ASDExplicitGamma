module

public import ASDExplicitGamma.Native.OldSignedSourceCellTraceLaw
public import ASDExplicitGamma.Native.OldSignedDescendantDirectionalMean
public import ASDExplicitGamma.Main.EnvelopeHTransport
public import ASDExplicitGamma.Inverse.MixedBridgeObsCellTrace
public import ASDExplicitGamma.Inverse.MixedBridgeLocalBudget

/-! Raw weak trace sequence of the scalar observer `Q_{m+129}` at depth `134 + j`:
tower identity, `L²` envelope, measurability, and mean. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse Native Gaussian Cold Algsuperdiff.Section3
  Numerics.Inverse ASDExplicitGamma.Main
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

theorem rawSeq_eq_avg (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (n : ℕ) :
    rawWeakTraceSequence M m Q t ω n =
      descendantsAverage Q n (fun R => rawCubeFourLoadTrace M m R t ω) := by
  unfold rawWeakTraceSequence descendantsAverage squareCellMean
  congr 1
  exact Finset.sum_coe_sort (descendantsAtDepth Q n)
    (fun R => rawCubeFourLoadTrace M m R t ω)

theorem trace_tower (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    rawWeakTraceSequence M m Q 0 ω (134 + j) =
      descendantsAverage Q 134 (fun U => rawWeakTraceSequence M m U 0 ω j) := by
  rw [rawSeq_eq_avg, descendantsAverage_add_eq_descendantsAverage_descendantsAverage]
  simp only [rawSeq_eq_avg]

/-- The `L²` envelope at the scalar observer. -/
theorem scalar_trace_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hstates : ∀ l ≤ m, nativeInductionState M h l)
    (Q : TriadicCube 2) (hQ : Q.scale = m + 129) (j : ℕ) :
    eLpNorm (fun ω => rawWeakTraceSequence M m Q 0 ω (134 + j)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j)) := by
  let I := SquareCells Q (134 + j)
  let C := theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)
  let d : ℝ := (descendantsAtDepth Q (134 + j)).card
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q (134 + j))
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcell (U : I) : eLpNorm (rawCubeFourLoadTrace M m U.val 0) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    apply old_signed_source_cell_trace_L2 M h hM hg m 5 j (by norm_num) 0
      ⟨le_rfl, zero_le_one⟩ hstates U.val
    rw [scale_eq_sub_of_mem_descendantsAtDepth U.property, hQ]
    push_cast
    ring
  have hh := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure 2
    (by norm_num) (fun U : I => rawCubeFourLoadTrace M m U.val 0)
    (fun _ => d⁻¹) (fun _ => C) (fun _ => inv_nonneg.mpr hd.le) (fun _ => hC) hcell
  have hcard : Fintype.card I = (descendantsAtDepth Q (134 + j)).card := by simp [I, SquareCells]
  have hsum : (∑ _U : I, d⁻¹ * C) = C := by
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    change d * (d⁻¹ * C) = C
    rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  have he : (fun ω => rawWeakTraceSequence M m Q 0 ω (134 + j)) =
      (fun ω => ∑ U : I, d⁻¹ * rawCubeFourLoadTrace M m U.val 0 ω) := by
    funext ω
    exact Finset.mul_sum _ _ _
  rw [he]
  rwa [hsum] at hh

end
end ASDExplicitGamma.Scalar
