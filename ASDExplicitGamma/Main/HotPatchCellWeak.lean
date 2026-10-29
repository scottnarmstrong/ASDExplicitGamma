module

public import ASDExplicitGamma.Main.HotPatchGap
public import ASDExplicitGamma.Main.HotAbelWeights
public import ASDExplicitGamma.Native.OldSignedCompatibleMeans
public import ASDExplicitGamma.Native.OldSignedEnergyPartition
public import ASDExplicitGamma.Native.OldSignedCellAverage

/-! Hot-patch trial, package A, cellwise form: `Vw² ≤ B* Δ` with the bank weights, from the
cellwise compatible coercivity and the monotone-weights dominance. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators

noncomputable section

/-- Cellwise weak bound for the patch drop: on every source cell the four-load weak energy
of the drop is at most the (cell) inverse history times the cell energy of the drop. -/
theorem hot_patch_drop_weak_bound_cell (Q : TriadicCube 2) (D : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q D) :
    ∑ c : BlockCoord 2, vectorWeakHaarEnergy U
        (fun x => (hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c) x).1) ≤
      oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U
            (openCubeSet_subset_of_mem_descendantsAtDepth hU) k)) *
        ∑ c : BlockCoord 2, oldSignedEnergyPairing U nu sigma
          (oldSignedCellCoefficient Q U
            (openCubeSet_subset_of_mem_descendantsAtDepth hU) k)
          (hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c))
          (hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c)) := by
  classical
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  let kU := oldSignedCellCoefficient Q U hsub k
  let aU := responseFramePlanarCoefficientField nu sigma kU
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) nu sigma hnu hsigma kU
  let Dc : BlockCoord 2 → Vec 2 → BlockVec 2 := fun c =>
    hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c)
  let Eu : BlockCoord 2 → ℝ := fun c => oldSignedEnergyPairing U nu sigma kU (Dc c) (Dc c)
  let E : ℝ := ∑ c, Eu c
  have hcomp (c : BlockCoord 2) : ScalarCompatible (openCubeSet U) (Dc c) :=
    old_signed_compatible_restrict Q U hsub
      (scalar_variation_compatible (hot_patch_drop_variation Q D nu sigma hnu hsigma k
        (blockBasis c)))
  have hEu0 (c : BlockCoord 2) : 0 ≤ Eu c :=
    old_signed_energy_pairing_nonneg U nu sigma hnu hsigma kU _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun c _ => hEu0 c
  have hF (c : BlockCoord 2) (i : Fin 2) :
      MemLp (fun x => (Dc c x).1 i) 2 (normalizedCubeMeasure U) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 (hcomp c).1) i)
  have hprojc (c : BlockCoord 2) (j : ℕ) :
      (∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))) ≤
        lemmaVInverseDepthMax U aU j * Eu c := by
    have h := compatible_projectionEnergy_bound hEll ⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩
      (hcomp c).2.1 (hcomp c).2.2 (hcomp c).1 j
    have hav : cubeAverage U (blockPairingIntegrand aU
        ⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩ ⟨fun x => (Dc c x).1, fun x => (Dc c x).2⟩) =
        Eu c := by
      rw [cubeAverage_eq_integralAverage_openCubeSet U]
      rfl
    rw [hav] at h
    exact h
  have hproj (j : ℕ) : (∑ c, ∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))) ≤
      lemmaVInverseDepthMax U aU j * E := by
    calc _ ≤ ∑ c, lemmaVInverseDepthMax U aU j * Eu c :=
          Finset.sum_le_sum fun c _ => hprojc c j
      _ = _ := by rw [← Finset.mul_sum]
  obtain ⟨hsum, hid⟩ := old_signed_finite_weak_projection_series U
    (fun c x => (Dc c x).1) hF
  rw [hid]
  have hα := Scalar.inverse_history_discount_range
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hqinv : ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ = Scalar.inverseHistoryDiscount :=
    (Scalar.inverse_history_discount_eq).symm
  have hs1 : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      lemmaVInverseDepthMax U aU j) := by
    have := lemmaVInverseHistory_summable U hEll hq
    rwa [hqinv] at this
  have hpow (j : ℕ) : Scalar.inverseHistoryDiscount ^ (2 * j) ≤ Scalar.inverseHistoryDiscount ^ j :=
    pow_le_pow_of_le_one hα.1.le hα.2.le (by omega)
  have hs2 : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      lemmaVInverseDepthMax U aU j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (by have := hα.1; positivity)
      (lemmaVInverseDepthMax_nonneg U aU j))
      (fun j => mul_le_mul_of_nonneg_right (hpow j) (lemmaVInverseDepthMax_nonneg U aU j)) hs1
  have hcmp : (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
      ∑ c, ∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))) ≤
      ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        (lemmaVInverseDepthMax U aU j * E) :=
    hsum.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hproj j) (by
      have := hα.1; positivity)) ((hs2.mul_right E).congr (fun j => by ring))
  have hfac : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  calc (1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        ∑ c, ∑ i, energy U (cubeProjection U j (fun x => (Dc c x).1 i))
      ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        (lemmaVInverseDepthMax U aU j * E) := mul_le_mul_of_nonneg_left hcmp hfac
    _ = ((1 - Scalar.inverseHistoryDiscount ^ 2) * ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
        lemmaVInverseDepthMax U aU j) * E := by
      rw [show (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          (lemmaVInverseDepthMax U aU j * E)) = (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          lemmaVInverseDepthMax U aU j) * E by
        rw [← tsum_mul_right]; exact tsum_congr fun j => by ring]
      ring
    _ ≤ oldSignedInverseHistory U aU * E :=
      mul_le_mul_of_nonneg_right (ASDExplicitGamma.Main.hot_weak_weights_le_inverse_history U aU hEll) hE0

/-- `Vw² ≤ B* Δ`: for any bound `Bmax` of the cell inverse histories, the tile-averaged weak
energy of the patch drop is at most `Bmax` times the trace subadditivity defect. -/
theorem hot_patch_drop_weak_bound_cells (Q : TriadicCube 2) (D : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (Bmax : ℝ)
    (hB : ∀ (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q D),
      oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma
        (oldSignedCellCoefficient Q U
          (openCubeSet_subset_of_mem_descendantsAtDepth hU) k)) ≤ Bmax) :
    descendantsAverage Q D (fun U => ∑ c : BlockCoord 2, vectorWeakHaarEnergy U
      (fun x => (hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c) x).1)) ≤
      Bmax * (descendantsAverage Q D (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q)
          (responseFramePlanarCoefficientField nu sigma k) 1) := by
  classical
  let Dc : BlockCoord 2 → Vec 2 → BlockVec 2 := fun c =>
    hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c)
  have hmem (c : BlockCoord 2) : MemBlockL2 (openCubeSet Q) (Dc c) := by
    have hS : MemBlockL2 (openCubeSet Q)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) :
          Vec 2 → BlockVec 2) := Lp.memLp _
    have hL := old_signed_local_residual_memLp Q D nu sigma hnu hsigma k
      (fun _ => blockBasis c) (memLp_const (blockBasis c))
    exact hS.sub hL
  have hid := hot_patch_drop_energy_sum Q D nu sigma hnu hsigma k
  have hpart (c : BlockCoord 2) := old_signed_energy_pairing_partition Q D nu sigma hnu hsigma
    k (hmem c) (hmem c)
  let Ecell : OldSignedCellIndex Q D → ℝ := fun U =>
    ∑ c : BlockCoord 2, oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (Dc c) (Dc c)
  have hE0 (U : OldSignedCellIndex Q D) : 0 ≤ Ecell U :=
    Finset.sum_nonneg fun c _ => old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma _ _
  rw [← old_signed_cell_average_eq_descendantsAverage
    (Q := Q) (depth := D) (f := fun U => ∑ c : BlockCoord 2, vectorWeakHaarEnergy U
      (fun x => (hotPatchDrop Q D nu sigma hnu hsigma k (blockBasis c) x).1))]
  calc oldSignedCellAverage Q D (fun U => ∑ c : BlockCoord 2, vectorWeakHaarEnergy U.val
        (fun x => (Dc c x).1))
      ≤ oldSignedCellAverage Q D (fun U => Bmax * Ecell U) := by
        apply old_signed_cell_average_mono
        intro U
        exact (hot_patch_drop_weak_bound_cell Q D nu sigma hnu hsigma k U.val U.property).trans
          (mul_le_mul_of_nonneg_right (hB U.val U.property) (hE0 U))
    _ = Bmax * oldSignedCellAverage Q D Ecell := old_signed_cell_average_mul Q D Bmax Ecell
    _ = Bmax * ∑ c : BlockCoord 2, oldSignedEnergyPairing Q nu sigma k (Dc c) (Dc c) := by
        congr 1
        simp only [Ecell]
        rw [old_signed_cell_average_sum Q D Finset.univ]
        exact Finset.sum_congr rfl fun c _ => (hpart c).symm
    _ = _ := by rw [hid]

end

end ASDExplicitGamma.Native
