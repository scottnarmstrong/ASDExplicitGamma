module

public import ASDExplicitGamma.Triadic.PlanarNeumannBridge
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ASDExplicitGamma.Variational.LemmaVTiles
public import ASDExplicitGamma.Native.BoundaryChargeFlatConstants

/-! Whole-parent versus fine-cell weak norms for the same physical field.
The exact shifted projection identity keeps every descendant depth. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

/-- Exact complete broken weak energy in terms of parent projections.
The local averages and all descendant Haar levels use the same field. -/
theorem parent_boundary_broken_weak_identity
    (Q : TriadicCube 2) (j : ℕ) {q : ℝ} (hq : 1 < q)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun U => dualEnergy U q f) =
      (1-q⁻¹) * ∑' k : ℕ, (q⁻¹)^k * energy Q (cubeProjection Q (j+k) f) := by
  let D := descendantsAtDepth Q j
  let r : ℝ := q⁻¹
  let localTerm : TriadicCube 2 → ℕ → ℝ := fun U k =>
    r ^ k * energy U (cubeProjection U k f)
  have hLocalLp : ∀ U ∈ D,
      MemLp f 2 (normalizedCubeMeasure U) := by
    intro U hU
    exact memLp_on_descendant_of_memLp hU hf
  have hlocalSummable : ∀ U ∈ D, Summable (localTerm U) := by
    intro U hU
    dsimp [localTerm, r]
    exact summable_weighted_projections U hq (hLocalLp U hU)
  have hswap : (∑' k : ℕ, ∑ U ∈ D, localTerm U k) =
      ∑ U ∈ D, ∑' k : ℕ, localTerm U k :=
    Summable.tsum_finsetSum hlocalSummable
  have hAvgProjection : ∀ k : ℕ,
      (D.card : ℝ)⁻¹ * ∑ U ∈ D,
          energy U (cubeProjection U k f) =
        energy Q (cubeProjection Q (j + k) f) := by
    intro k
    change descendantsAverage Q j
        (fun U => energy U (cubeProjection U k f)) = _
    exact descendantsAverage_localProjection_eq Q j k f
  have hExpansion : descendantsAverage Q j
      (fun U => dualEnergy U q f) =
      (1 - r) * ∑' k : ℕ, r ^ k *
        energy Q (cubeProjection Q (j + k) f) := by
    unfold descendantsAverage
    dsimp [D]
    rw [Finset.sum_congr rfl fun U hU =>
      dualEnergy_eq U hq (hLocalLp U hU)]
    calc
      (↑(descendantsAtDepth Q j).card)⁻¹ *
          ∑ U ∈ descendantsAtDepth Q j,
            ((1 - q⁻¹) * ∑' k : ℕ, q⁻¹ ^ k *
              energy U (cubeProjection U k f))
          = (1 - r) * ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
              ∑ U ∈ descendantsAtDepth Q j, ∑' k : ℕ, localTerm U k) := by
                simp only [localTerm, r]
                rw [← Finset.mul_sum]
                ring
      _ = (1 - r) * ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑' k : ℕ, ∑ U ∈ descendantsAtDepth Q j, localTerm U k) := by
              rw [← hswap]
      _ = (1 - r) * ∑' k : ℕ, r ^ k *
            energy Q (cubeProjection Q (j + k) f) := by
              rw [← tsum_mul_left]
              apply congrArg (fun t : ℝ => (1 - r) * t)
              apply tsum_congr
              intro k
              calc
                (↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
                    ∑ U ∈ descendantsAtDepth Q j, localTerm U k =
                  r ^ k * ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
                    ∑ U ∈ descendantsAtDepth Q j,
                      energy U (cubeProjection U k f)) := by
                        dsimp [localTerm]
                        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                        refine Finset.sum_congr rfl fun U hU => ?_
                        ring
                _ = r ^ k * energy Q (cubeProjection Q (j + k) f) := by
                      rw [hAvgProjection k]
  exact hExpansion

/-- Restricting the same field to a finite cell partition increases its
broken weak energy. This is the direction needed by the parent source. -/
theorem parent_boundary_weak_le_broken
    (Q : TriadicCube 2) (j : ℕ) {q : ℝ} (hq : 1 < q)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q q f ≤ descendantsAverage Q j (fun U => dualEnergy U q f) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).2 hq
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_right (energy Q f)
  have hshift : Summable (fun k : ℕ => (q⁻¹)^k * energy Q (cubeProjection Q (j+k) f)) := by
    apply hgeom.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr0 _) (energy_nonneg Q _))]
    exact mul_le_mul_of_nonneg_left
      (energy_projection_le Q (j+k) hf) (pow_nonneg hr0 _)
  rw [dualEnergy_eq Q hq hf, parent_boundary_broken_weak_identity Q j hq hf]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hr1.le)
  apply (summable_weighted_projections Q hq hf).tsum_le_tsum _ hshift
  intro k
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
  have hh := energy_projection_le Q k (projection_memLp Q (j+k) f 2)
  rw [projection_projection Q k (j+k) hf, min_eq_left (by omega : k ≤ j+k)] at hh
  exact hh

/-- Vector parent weak energy is dominated by the exact broken weak energy
of the same physical vector field on the fine cells. -/
theorem parent_boundary_vector_weak_le_broken
    (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → Vec 2)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarNorm Q F^2 ≤ lemmaVTiledWeakEnergy Q j F := by
  rw [vectorWeakHaarNorm, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q F)]
  simp only [lemmaVTiledWeakEnergy, vectorWeakHaarEnergy]
  rw [descendantsAverage_sum]
  apply Finset.sum_le_sum
  intro i _
  apply parent_boundary_weak_le_broken Q j _ (hF i)
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]

private theorem parentCD_le : planarCD ≤ (52/100:ℝ) := by
  have hpi : (3:ℝ) ≤ Real.pi := le_of_lt (by linarith [Real.pi_gt_d20])
  have hden : (18:ℝ) ≤ 2*Real.pi^2 := by nlinarith only [hpi]
  have hfrac : 1/(2*Real.pi^2) ≤ (1/18:ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hden
  have hc1 := pow_le_pow_left₀ (Real.sqrt_nonneg _)
    native_boundary_planarC1_le 2
  change planarC1^2 ≤ (304/1000:ℝ)^2 at hc1
  have hsq := planarCD_sq
  nlinarith only [hc1, hfrac, hsq, show 0 ≤ planarCD from Real.sqrt_nonneg _]

/-- Source parent Dirichlet weak Poincare estimate at any independent fine
comparison depth. The H10 field is the actual parent potential; no affine
boundary condition is imposed on its restrictions to the cells. -/
theorem parent_boundary_h10_l2_sq
    (Q : TriadicCube 2) (j : ℕ) (u : H10Function (openCubeSet Q)) :
    energy Q u.toH1Function.toFun ≤
      (52/100:ℝ)^2 * cubeScaleFactor Q^2 *
        lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  have hglobal := dirichlet_L2_bridge_sq Q u
  have hbroken := parent_boundary_vector_weak_le_broken Q j u.toH1Function.grad
    u.toH1Function.grad_memL2_normalizedCubeMeasure
  have hc := pow_le_pow_left₀ (Real.sqrt_nonneg _) parentCD_le 2
  calc
    _ ≤ cubeScaleFactor Q^2 * planarCD^2 * vectorWeakHaarNorm Q u.toH1Function.grad^2 := hglobal
    _ ≤ cubeScaleFactor Q^2 * (52/100:ℝ)^2 * vectorWeakHaarNorm Q u.toH1Function.grad^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) (sq_nonneg _)
    _ ≤ cubeScaleFactor Q^2 * (52/100:ℝ)^2 * lemmaVTiledWeakEnergy Q j u.toH1Function.grad :=
      mul_le_mul_of_nonneg_left hbroken (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

end
end ASDExplicitGamma.Native
