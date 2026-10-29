module

public import ASDExplicitGamma.Scalar.PairWeakTriangle
public import ASDExplicitGamma.Scalar.PairInnerMain
public import ASDExplicitGamma.Native.OldSignedDescendantMinkowski

/-! Constant-one Minkowski for the tiled weak budget of a sum of two fields (the forced and the
inner part of the first-response defect), summed over modes. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open scoped BigOperators

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- Pair of weak energies of a vector pair on one cell, summed. -/
theorem cell_split (U : TriadicCube 2) {fx ix dx fy iy dy : Vec 2 → Vec 2}
    (hfx : ∀ i, MemLp (fun x => fx x i) 2 (normalizedCubeMeasure U))
    (hix : ∀ i, MemLp (fun x => ix x i) 2 (normalizedCubeMeasure U))
    (hfy : ∀ i, MemLp (fun x => fy x i) 2 (normalizedCubeMeasure U))
    (hiy : ∀ i, MemLp (fun x => iy x i) 2 (normalizedCubeMeasure U))
    (hx : vectorWeakHaarEnergy U dx = vectorWeakHaarEnergy U (fun x i => fx x i + ix x i))
    (hy : vectorWeakHaarEnergy U dy = vectorWeakHaarEnergy U (fun x i => fy x i + iy x i)) :
    Real.sqrt (vectorWeakHaarEnergy U dx + vectorWeakHaarEnergy U dy) ≤
      Real.sqrt (vectorWeakHaarEnergy U fx + vectorWeakHaarEnergy U fy) +
        Real.sqrt (vectorWeakHaarEnergy U ix + vectorWeakHaarEnergy U iy) := by
  have tx := vectorWeakHaarNorm_add_le U hfx hix
  have ty := vectorWeakHaarNorm_add_le U hfy hiy
  have nsq (F : Vec 2 → Vec 2) : vectorWeakHaarNorm U F = Real.sqrt (vectorWeakHaarEnergy U F) := rfl
  rw [nsq, nsq, nsq, ← hx] at tx
  rw [nsq, nsq, nsq, ← hy] at ty
  have h := old_signed_finite_sqrt_sq_bound (I := Fin 2)
    (fun b => if b = 0 then Real.sqrt (vectorWeakHaarEnergy U fx) else Real.sqrt (vectorWeakHaarEnergy U fy))
    (fun b => if b = 0 then Real.sqrt (vectorWeakHaarEnergy U ix) else Real.sqrt (vectorWeakHaarEnergy U iy))
    (fun b => if b = 0 then Real.sqrt (vectorWeakHaarEnergy U dx) else Real.sqrt (vectorWeakHaarEnergy U dy))
    (fun b => by split_ifs <;> exact Real.sqrt_nonneg _)
    (fun b => by split_ifs <;> assumption)
  simp only [Fin.sum_univ_two, if_pos, Fin.one_eq_zero_iff, one_ne_zero, if_false, Nat.succ_ne_self,
    Fin.isValue] at h
  rw [Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _), Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _),
    Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _), Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _),
    Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _), Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _)] at h
  exact h

theorem memLp_cell (Q U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q 134) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (i : Fin 2) :
    MemLp (fun x => F x i) 2 (normalizedCubeMeasure U) :=
  memLp_normalized_of_memL2On (memL2On_mono (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    (hF.eval i))

theorem sum_split (Q : TriadicCube 2) {J : ℕ} (fx ix dx fy iy dy : Fin J → Vec 2 → Vec 2)
    (mfx : ∀ j, MemVectorL2 (openCubeSet Q) (fx j)) (mix : ∀ j, MemVectorL2 (openCubeSet Q) (ix j))
    (mfy : ∀ j, MemVectorL2 (openCubeSet Q) (fy j)) (miy : ∀ j, MemVectorL2 (openCubeSet Q) (iy j))
    (hx : ∀ j, dx j =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x i => fx j x i + ix j x i)
    (hy : ∀ j, dy j =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x i => fy j x i + iy j x i) :
    Real.sqrt (∑ j, lemmaVTiledWeakEnergy Q 134 (dx j) + ∑ j, lemmaVTiledWeakEnergy Q 134 (dy j)) ≤
      Real.sqrt (∑ j, lemmaVTiledWeakEnergy Q 134 (fx j) + ∑ j, lemmaVTiledWeakEnergy Q 134 (fy j)) +
        Real.sqrt (∑ j, lemmaVTiledWeakEnergy Q 134 (ix j) + ∑ j, lemmaVTiledWeakEnergy Q 134 (iy j)) := by
  classical
  have hW0 : ∀ (F : Vec 2 → Vec 2) (U : TriadicCube 2), 0 ≤ vectorWeakHaarEnergy U F :=
    fun F U => vectorWeakHaarEnergy_nonneg U F
  let E : Fin J → TriadicCube 2 → ℝ := fun j U => vectorWeakHaarEnergy U (fx j) + vectorWeakHaarEnergy U (fy j)
  let G : Fin J → TriadicCube 2 → ℝ := fun j U => vectorWeakHaarEnergy U (ix j) + vectorWeakHaarEnergy U (iy j)
  let D : Fin J → TriadicCube 2 → ℝ := fun j U => vectorWeakHaarEnergy U (dx j) + vectorWeakHaarEnergy U (dy j)
  have tile : ∀ j, Real.sqrt (descendantsAverage Q 134 (D j)) ≤
      Real.sqrt (descendantsAverage Q 134 (E j)) + Real.sqrt (descendantsAverage Q 134 (G j)) := by
    intro j
    have h := old_signed_descendant_sqrt_energy_bound Q 134 (E j) (G j)
      (fun U => Real.sqrt (D j U)) (A := 1) (B := 1) zero_le_one zero_le_one
      (fun U _ => add_nonneg (hW0 _ _) (hW0 _ _)) (fun U _ => add_nonneg (hW0 _ _) (hW0 _ _))
      (fun U _ => Real.sqrt_nonneg _) (fun U hU => by
        rw [one_mul, one_mul]
        refine cell_split U (memLp_cell Q U hU (mfx j)) (memLp_cell Q U hU (mix j))
          (memLp_cell Q U hU (mfy j)) (memLp_cell Q U hU (miy j)) ?_ ?_
        · apply (smooth_feedback_vector_weak_energy_congr_ae U ?_)
          exact ae_mono (Measure.restrict_mono_set volume
            (openCubeSet_subset_of_mem_descendantsAtDepth hU)) (hx j)
        · apply (smooth_feedback_vector_weak_energy_congr_ae U ?_)
          exact ae_mono (Measure.restrict_mono_set volume
            (openCubeSet_subset_of_mem_descendantsAtDepth hU)) (hy j))
    have hsq : descendantsAverage Q 134 (fun U => Real.sqrt (D j U) ^ 2) =
        descendantsAverage Q 134 (D j) := by
      unfold descendantsAverage
      apply congrArg (fun z : ℝ => ((descendantsAtDepth Q 134).card : ℝ)⁻¹ * z)
      exact Finset.sum_congr rfl fun U _ => Real.sq_sqrt (add_nonneg (hW0 _ _) (hW0 _ _))
    rw [hsq] at h
    simpa using h
  have avgnn : ∀ F : TriadicCube 2 → ℝ, (∀ U, 0 ≤ F U) → 0 ≤ descendantsAverage Q 134 F :=
    fun F hF => descendantsAverage_nonneg Q _ _ (fun U _ => hF U)
  have hEn : ∀ j, 0 ≤ descendantsAverage Q 134 (E j) := fun j =>
    avgnn _ (fun U => add_nonneg (hW0 _ _) (hW0 _ _))
  have hGn : ∀ j, 0 ≤ descendantsAverage Q 134 (G j) := fun j =>
    avgnn _ (fun U => add_nonneg (hW0 _ _) (hW0 _ _))
  have hDn : ∀ j, 0 ≤ descendantsAverage Q 134 (D j) := fun j =>
    avgnn _ (fun U => add_nonneg (hW0 _ _) (hW0 _ _))
  have hfin := old_signed_finite_sqrt_sq_bound (I := Fin J)
    (fun j => Real.sqrt (descendantsAverage Q 134 (E j)))
    (fun j => Real.sqrt (descendantsAverage Q 134 (G j)))
    (fun j => Real.sqrt (descendantsAverage Q 134 (D j)))
    (fun j => Real.sqrt_nonneg _) tile
  simp only [Real.sq_sqrt (hEn _), Real.sq_sqrt (hGn _), Real.sq_sqrt (hDn _)] at hfin
  have eq (X : Fin J → Vec 2 → Vec 2) (Y : Fin J → Vec 2 → Vec 2) :
      ∑ j, descendantsAverage Q 134 (fun U => vectorWeakHaarEnergy U (X j) + vectorWeakHaarEnergy U (Y j)) =
        ∑ j, lemmaVTiledWeakEnergy Q 134 (X j) + ∑ j, lemmaVTiledWeakEnergy Q 134 (Y j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold lemmaVTiledWeakEnergy
    rw [descendantsAverage_add]
  have e1 := eq dx dy
  have e2 := eq fx fy
  have e3 := eq ix iy
  simp only [D, E, G] at hfin
  rw [e1, e2, e3] at hfin
  exact hfin

end

end ASDExplicitGamma.Scalar
