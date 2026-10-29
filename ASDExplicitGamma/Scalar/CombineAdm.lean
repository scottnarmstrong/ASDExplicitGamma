module

public import ASDExplicitGamma.Scalar.CombineH1
public import ASDExplicitGamma.Scalar.RefQuartBound
public import ASDExplicitGamma.Native.OldSignedFlatAdmissibility

/-! Cell admissibility of the flat field at depth 134 of the big cube. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem normalizedCubeMeasure_ac_descendant {Q U : TriadicCube 2} {j : ℕ}
    (hU : U ∈ descendantsAtDepth Q j) :
    normalizedCubeMeasure U ≪ normalizedCubeMeasure Q := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have h1 : volumeMeasureOn (openCubeSet U) ≤ volumeMeasureOn (openCubeSet Q) :=
    Measure.restrict_mono hsub le_rfl
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  intro s hs
  rw [normalizedCubeMeasure_eq_smul_open Q] at hs
  have hs' : volumeMeasureOn (openCubeSet Q) s = 0 := by
    simpa [Measure.smul_apply, hc] using hs
  have h2 : volumeMeasureOn (openCubeSet U) s = 0 :=
    le_antisymm (hs' ▸ h1 s) bot_le
  rw [normalizedCubeMeasure_eq_smul_open U]
  simp [Measure.smul_apply, h2]

namespace Cfg''

section Flat

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

include hQ in
/-- The flat field is admissible on every depth-134 cell of the big cube. -/
theorem flatCellAdm (ω : Cutoff.CutoffSample 2) : FlatCellAdm m hab hcd e ω := by
  intro U hU
  obtain ⟨G, hG⟩ := flat_wick_h1_components (originCube 2 (m + 129)) hab hcd hQ e m ω
  have hac := normalizedCubeMeasure_ac_descendant hU
  let Gu : Fin 2 → H1Function (openCubeSet U) := fun i => (G i).restrictToOpenSubcube hU
  have hae : ∀ i, (fun x => Gu i x) =ᵐ[normalizedCubeMeasure U]
      fun x => flatField (originCube 2 (m + 129)) hab hcd e m ω x i :=
    fun i => hac.ae_le (hG i)
  have hFeq : (fun x => flatField (originCube 2 (m + 129)) hab hcd e m ω x) =ᵐ[normalizedCubeMeasure U]
      fun x i => Gu i x := by
    have : ∀ᵐ x ∂(normalizedCubeMeasure U), ∀ i, Gu i x =
        flatField (originCube 2 (m + 129)) hab hcd e m ω x i :=
      ae_all_iff.2 hae
    filter_upwards [this] with x hx
    funext i
    exact (hx i).symm
  refine ⟨?_, fun i => ?_⟩
  · have hmem : MemLp (fun x i => Gu i x) 2 (normalizedCubeMeasure U) :=
      MemLp.of_eval fun i => (Gu i).memL2_normalizedCubeMeasure
    exact hmem.ae_eq hFeq.symm
  · have hs := old_signed_h1_vector_positive_summable U Gu i
    have hinc : ∀ j, cubeIncrement U (j + 1)
        (fun x => flatField (originCube 2 (m + 129)) hab hcd e m ω x i) =
        cubeIncrement U (j + 1) (fun x => Gu i x) := fun j =>
      cubeIncrement_congr_ae U (j + 1) (hae i).symm
    simpa only [hinc] using hs

end Flat

end Cfg''

end

end ASDExplicitGamma.Scalar
