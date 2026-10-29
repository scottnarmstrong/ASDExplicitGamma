module

public import ASDExplicitGamma.Native.GenericSourceBandRawProfile
public import ASDExplicitGamma.Cold.NativeSubadditivity

/-! Source caps on actual common descendant averages and coarse cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Cold ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Finite spatial averaging preserves a common prime L20 cap; the full
population cardinal cancels, without an independence premise. -/
theorem native_source_average_L20_cap
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (A : ℝ) (_hA : 0 ≤ A) (hcap : ∀ i, eLpNorm' (X i) 20 μ ≤ ENNReal.ofReal A) :
    eLpNorm' (fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)) 20 μ ≤ ENNReal.ofReal A := by
  let S := fun ω => ∑ i, X i ω
  let c : ℝ := (Fintype.card ι:ℝ)⁻¹
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hc : 0 ≤ c := inv_nonneg.mpr hn.le
  have hsumeq : S=∑ i, X i := by funext ω; simp only [S,Finset.sum_apply]
  have hsum : eLpNorm' S 20 μ ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*A) := by
    rw [hsumeq]
    have hh := (eLpNorm'_sum_le (s := Finset.univ) (fun i _ => hX i) (by norm_num : (1:ℝ)≤20)).trans
      (Finset.sum_le_sum (fun i _ => hcap i))
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ENNReal.ofReal_mul hn.le,ENNReal.ofReal_natCast] using hh
  have hefun : c • S=(fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)) := by
    funext ω
    dsimp [c,S]
    simp only [div_eq_mul_inv,mul_comm]
  have hscale := eLpNorm'_const_smul (f := S) c (μ := μ) (by norm_num : (0:ℝ)<20)
  rw [hefun,Real.enorm_eq_ofReal hc] at hscale
  rw [hscale]
  calc
    _ ≤ ENNReal.ofReal c*ENNReal.ofReal ((Fintype.card ι:ℝ)*A) := mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (c*((Fintype.card ι:ℝ)*A)) := (ENNReal.ofReal_mul hc).symm
    _ = _ := by congr 1; dsimp [c]; field_simp

/-- Every translated actual cell has exactly the origin prime L20 cap,
in the same completed law and true frame. -/
theorem native_source_cell_L20_cap (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (A : ℝ) (hcap : eLpNorm' (cutoffTraceDefect M m Q.scale) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal A) :
    eLpNorm' (coldNativeCellTrace M m Q) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal A := by
  have he := (coldNativeCellTrace_identDistrib M m Q).eLpNorm_eq (p := (20:ℝ≥0∞))
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num : (20:ℝ≥0∞)≠⊤)
      (coldNativeCellTrace_measurable M m Q).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num : (20:ℝ≥0∞)≠⊤)
      (cutoffTraceDefect_measurable M m Q.scale).aestronglyMeasurable] at he
  exact he.le.trans hcap

/-- Actual coarse subadditivity transfers a fine-cell cap to its parent.
Every descendant is in the same cutoff law; no truncated-law replacement occurs. -/
theorem native_source_parent_L20_cap (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hcap : eLpNorm' (cutoffTraceDefect M m (Q.scale-(r:ℤ))) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal A) :
    eLpNorm' (cutoffTraceDefect M m Q.scale) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal A := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun (R : SquareCells Q r) => coldNativeCellTrace M m R.val
  let avg := fun ω => squareCellMean Q r (fun R => X R ω)
  have hcell (R : SquareCells Q r) : eLpNorm' (X R) 20 μ ≤ ENNReal.ofReal A := by
    apply native_source_cell_L20_cap M m R.val A
    rw [scale_eq_sub_of_mem_descendantsAtDepth R.property]
    exact hcap
  have havg : eLpNorm' avg 20 μ ≤ ENNReal.ofReal A := by
    have hh := native_source_average_L20_cap μ X
      (fun R => (coldNativeCellTrace_measurable M m R.val).aestronglyMeasurable) A hA hcell
    have hefun : avg=(fun ω => (∑ R, X R ω)/(Fintype.card (SquareCells Q r):ℝ)) := by
      funext ω
      dsimp [avg,squareCellMean]
      rw [Fintype.card_coe]
      ring
    rw [hefun]
    exact hh
  have hparent : eLpNorm' (coldNativeCellTrace M m Q) 20 μ ≤ ENNReal.ofReal A := by
    apply (eLpNorm'_mono_ae (by norm_num : (0:ℝ)≤20) _).trans havg
    exact Filter.Eventually.of_forall fun ω => by
      have h0 := coldNativeCellTrace_nonneg M m Q ω
      have hsub := coldNativeCellTrace_subadditive M m Q r ω
      rw [Real.norm_of_nonneg h0,Real.norm_of_nonneg (h0.trans hsub)]
      exact hsub
  have he := (coldNativeCellTrace_identDistrib M m Q).eLpNorm_eq (p := (20:ℝ≥0∞))
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num : (20:ℝ≥0∞)≠⊤)
      (coldNativeCellTrace_measurable M m Q).aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num : (20:ℝ≥0∞)≠⊤)
      (cutoffTraceDefect_measurable M m Q.scale).aestronglyMeasurable] at he
  exact he.ge.trans hparent

end
end ASDExplicitGamma.Native
