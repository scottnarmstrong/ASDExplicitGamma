module

public import ASDExplicitGamma.Triadic.PlanarDirectionOperations

/-! Conversion of genuine normalized-cell L-infinity witnesses to volume witnesses. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

 theorem hilbert_memLp_open_of_normalized_any {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {u : Vec d → E} {p : ℝ≥0∞} (hu : MemLp u p (normalizedCubeMeasure Q)) :
    MemLp u p (volume.restrict (openCubeSet Q)) := by
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have h : volume.restrict (cubeSet Q) ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
    have hc : ENNReal.ofReal (cubeVolume Q)*ENNReal.ofReal (cubeVolume Q)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (cubeVolume_nonneg Q), mul_inv_cancel₀ (cubeVolume_pos Q).ne', ENNReal.ofReal_one]
    rw [hc, one_smul]
  exact hu.of_measure_le_smul ENNReal.ofReal_ne_top h

 theorem PlanarW2Infinity.gradient_memLp_top_volume {Q : TriadicCube 2} (η : PlanarW2Infinity Q) (i : Fin 2) :
    MemLp (fun x => η.value.grad x i) ⊤ (volume.restrict (openCubeSet Q)) := by
  rw [← η.gradient_eq i]
  exact hilbert_memLp_open_of_normalized_any Q (η.gradient.component_memLp_top i)

end
end ASDExplicitGamma.Triadic
