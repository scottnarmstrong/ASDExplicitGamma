module

public import ASDExplicitGamma.Scalar.PairWeakBound

/-! The tiled weak energy of the pair-space solution of a two-slot source, with the exact
constant `D = 1 + 3^{-1/4}` (energy constant one, circle energy at most positive energy). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance weakMainFinite (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- **Pair-space weak energy.** For the pair-space solution `(Y, X)` of the paired source
`(s₁, s₂)` with slot fields `(F, G)`, the tiled weak energies of the gradients of its two
potentials obey `W(∇φ) + W(∇η) ≤ ((1 + 3^{-1/4}) B*)² (P(F) + P(G))`. -/
theorem pair_weak_energy_bound (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ} (hν : 0 < ν)
    (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hGc : ∀ U ∈ descendantsAtDepth Q n, MemLp G 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => G x i))))
    (s₁ : HilbertVectorL2 (openCubeSet Q)) (s₂ : (physicalPotentialSpace Q).toSubmodule)
    (hs1 : s₁ ∈ (physicalFluxSpace Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ)
    (hs2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ)
    {Bstar : ℝ} (hBs : 0 ≤ Bstar)
    (hB : ∀ U ∈ descendantsAtDepth Q n, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    ∃ (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q)),
      φ.toH1Function.gradToHilbertVectorL2 =
          (twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q)) ∧
      η.gradToHilbertVectorL2 = twoSlotY Q hν hσ k s₁ s₂ ∧
      lemmaVTiledWeakEnergy Q n φ.toH1Function.grad + lemmaVTiledWeakEnergy Q n η.grad ≤
        ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 *
          (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G) := by
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  obtain ⟨φ, η, hc, hd, -, -, hnorm, hxφ, hyη, -⟩ := two_slot_parent_core_links Q hν hσ k hF hG
    s₁ (twoSlotY Q hν hσ k s₁ s₂) s₂ (twoSlotX Q hν hσ k s₁ s₂) hs1 hs1' hs2'
    (twoSlot_eq1 Q hν hσ k s₁ s₂) (twoSlot_eq2 Q hν hσ k s₁ s₂)
  refine ⟨φ, η, hxφ, hyη, ?_⟩
  set Bf : TriadicCube 2 → ℝ := fun U => lemmaVInverseHistory U
    (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) with hBf
  have hB0 : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ Bf U := fun U _ =>
    lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  set cc : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ)) with hcc
  have hc0 : 0 ≤ cc := by positivity
  have hPos : ∀ (H : Vec 2 → Vec 2) (U : TriadicCube 2), 0 ≤ vectorPositiveHaarEnergy U H :=
    fun H U => vectorPositiveHaarEnergy_nonneg U H
  have hPF : lemmaVTiledPositiveEnergy Q n F =
      descendantsAverage Q n (fun U => vectorPositiveHaarEnergy U F) := rfl
  have hPG : lemmaVTiledPositiveEnergy Q n G =
      descendantsAverage Q n (fun U => vectorPositiveHaarEnergy U G) := rfl
  have hPF0 : 0 ≤ lemmaVTiledPositiveEnergy Q n F := by
    rw [hPF]; unfold descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => hPos F U)
  have hPG0 : 0 ≤ lemmaVTiledPositiveEnergy Q n G := by
    rw [hPG]; unfold descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => hPos G U)
  -- the pair energy is at most `B* (P F + P G)` (constant one)
  have hz1 : (0 : HilbertVectorL2 (openCubeSet Q)) ∈ (physicalFluxSpace Q).toSubmodule :=
    Submodule.zero_mem _
  have hZc : ∀ U ∈ descendantsAtDepth Q n, MemLp zeroField 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) :=
    fun U _ => ⟨zeroField_memLp U, fun i => zeroField_pos U i⟩
  have hZ0 : ∀ w : HilbertVectorL2 (openCubeSet Q),
      ⟪toHilbertVectorL2OfVecField (zeroField_memL2 (openCubeSet Q)), w⟫_ℝ = 0 :=
    fun w => inner_zeroField w
  have hP1 := pure_energy_le Q n hν hσ k hF (zeroField_memL2 (openCubeSet Q)) hFc hZc
    (fun U _ => by rw [zeroField_energy]; simp) s₁ 0 hs1 hs1'
    (fun w => by rw [hZ0]; simp)
  have hP2 := pure_energy_le Q n hν hσ k (zeroField_memL2 (openCubeSet Q)) hG hZc hGc
    (fun U _ => by rw [zeroField_energy]; simp) 0 s₂ hz1
    (fun w _ => by rw [hZ0]; simp) hs2'
  have hEn := avg_energy (ν := ν) (σ := σ) Q n φ η
  have hE : pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) =
      (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) := by
    rw [hEn, twoSlot_energy_norm, hnorm]
  rw [twoSlot_energy_split] at hE
  set Eu : TriadicCube 2 → ℝ := fun U => volumeAverage (openCubeSet U) (fun z => (ν / σ) *
    (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) with hEu
  set ebar := descendantsAverage Q n Eu with hebar
  set W := descendantsAverage Q n (fun U => Bf U * (vectorPositiveHaarEnergy U F +
    vectorPositiveHaarEnergy U G)) with hW
  have hWsplit : W = descendantsAverage Q n (fun U => Bf U * (vectorPositiveHaarEnergy U F +
        vectorPositiveHaarEnergy U zeroField)) +
      descendantsAverage Q n (fun U => Bf U * (vectorPositiveHaarEnergy U zeroField +
        vectorPositiveHaarEnergy U G)) := by
    rw [← descendantsAverage_add, hW]
    congr 1
    funext U
    rw [zeroField_energy]
    ring
  have hebarW : ebar ≤ W := by
    have h12 := add_le_add hP1 hP2
    rw [← mul_add, ← hWsplit, hE] at h12
    exact le_of_mul_le_mul_left h12 hvol
  have hWB : W ≤ Bstar * (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G) := by
    have h1 : W ≤ descendantsAverage Q n (fun U => Bstar * (vectorPositiveHaarEnergy U F +
        vectorPositiveHaarEnergy U G)) := by
      rw [hW]
      apply descendantsAverage_le
      intro U hU
      exact mul_le_mul_of_nonneg_right (hB U hU) (add_nonneg (hPos F U) (hPos G U))
    rw [descendantsAverage_mul_left, descendantsAverage_add] at h1
    exact h1
  have hEu0 : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ Eu U := by
    intro U hU
    simp only [hEu]
    unfold volumeAverage
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro z
    exact mul_nonneg (div_pos hν hσ).le (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))
  -- cell data
  have hcell : ∀ U ∈ descendantsAtDepth Q n, ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧
      X + Y ≤ Bf U * Eu U ∧
      Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) ≤ Real.sqrt X +
        cc * Bf U * Real.sqrt (forcedSourceCircleEnergy U F) ∧
      Real.sqrt (vectorWeakHaarEnergy U η.grad) ≤ Real.sqrt Y +
        cc * Bf U * Real.sqrt (forcedSourceCircleEnergy U G) :=
    fun U hU => two_slot_cell_bound n hν hσ k φ η hG hc hd U hU (hFc U hU).1
      (hFc U hU).2 (hGc U hU).1 (hGc U hU).2
  choose! X Y hX hY hXY h1 h2 using hcell
  have hcellW : ∀ U ∈ descendantsAtDepth Q n,
      vectorWeakHaarEnergy U φ.toH1Function.grad + vectorWeakHaarEnergy U η.grad ≤
        (Real.sqrt (X U + Y U) + cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F +
          vectorPositiveHaarEnergy U G)) ^ 2 := by
    intro U hU
    have cF : Real.sqrt (forcedSourceCircleEnergy U F) ≤ Real.sqrt (vectorPositiveHaarEnergy U F) :=
      Real.sqrt_le_sqrt (pureFlux_forcedSourceCircleEnergy_le U F)
    have cG : Real.sqrt (forcedSourceCircleEnergy U G) ≤ Real.sqrt (vectorPositiveHaarEnergy U G) :=
      Real.sqrt_le_sqrt (pureFlux_forcedSourceCircleEnergy_le U G)
    have hccB : 0 ≤ cc * Bf U := mul_nonneg hc0 (hB0 U hU)
    have w1 := (h1 U hU).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left cF hccB))
    have w2 := (h2 U hU).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left cG hccB))
    have hsa := (Real.sqrt_le_iff.1 w1).2
    have hsb := (Real.sqrt_le_iff.1 w2).2
    have hPF := hPos F U
    have hPG := hPos G U
    have hab : (cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F)) ^ 2 +
        (cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U G)) ^ 2 =
        (cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F +
          vectorPositiveHaarEnergy U G)) ^ 2 := by
      have hm : ∀ t : ℝ, (cc * Bf U * Real.sqrt t) ^ 2 = (cc * Bf U) ^ 2 * Real.sqrt t ^ 2 :=
        fun t => mul_pow _ _ _
      rw [hm, hm, hm, Real.sq_sqrt hPF, Real.sq_sqrt hPG, Real.sq_sqrt (add_nonneg hPF hPG)]
      ring
    have key := two_comp_sq (Real.sqrt (X U)) (Real.sqrt (Y U))
      (cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F))
      (cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U G))
      (cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G))
      (mul_nonneg hccB (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (mul_nonneg hccB (Real.sqrt_nonneg _)) (mul_nonneg hccB (Real.sqrt_nonneg _)) hab
    rw [Real.sq_sqrt (hX U hU), Real.sq_sqrt (hY U hU)] at key
    linarith
  -- tile averages
  have h3 : descendantsAverage Q n (fun U => vectorWeakHaarEnergy U φ.toH1Function.grad +
      vectorWeakHaarEnergy U η.grad) ≤ descendantsAverage Q n (fun U =>
        (Real.sqrt (X U + Y U) + cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F +
          vectorPositiveHaarEnergy U G)) ^ 2) := descendantsAverage_le hcellW
  have h4 := avg_minkowski Q n (fun U => Real.sqrt (X U + Y U))
    (fun U => cc * Bf U * Real.sqrt (vectorPositiveHaarEnergy U F +
      vectorPositiveHaarEnergy U G))
  set P : ℝ := lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G with hP
  have hP0 : 0 ≤ P := add_nonneg hPF0 hPG0
  have hA1 : descendantsAverage Q n (fun U => Real.sqrt (X U + Y U) ^ 2) ≤ Bstar ^ 2 * P := by
    have c1 : descendantsAverage Q n (fun U => Real.sqrt (X U + Y U) ^ 2) ≤
        descendantsAverage Q n (fun U => Bstar * Eu U) := by
      apply descendantsAverage_le
      intro U hU
      rw [Real.sq_sqrt (add_nonneg (hX U hU) (hY U hU))]
      exact (hXY U hU).trans (mul_le_mul_of_nonneg_right (hB U hU) (hEu0 U hU))
    rw [descendantsAverage_mul_left] at c1
    calc _ ≤ Bstar * ebar := c1
      _ ≤ Bstar * (Bstar * P) :=
        mul_le_mul_of_nonneg_left (hebarW.trans hWB) hBs
      _ = Bstar ^ 2 * P := by ring
  have hA2 : descendantsAverage Q n (fun U => (cc * Bf U * Real.sqrt
      (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) ^ 2) ≤
        (cc * Bstar) ^ 2 * P := by
    have c1 : descendantsAverage Q n (fun U => (cc * Bf U * Real.sqrt
        (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) ^ 2) ≤
        descendantsAverage Q n (fun U => (cc * Bstar) ^ 2 * (vectorPositiveHaarEnergy U F +
          vectorPositiveHaarEnergy U G)) := by
      apply descendantsAverage_le
      intro U hU
      rw [mul_pow, Real.sq_sqrt (add_nonneg (hPos F U) (hPos G U))]
      have hb : cc * Bf U ≤ cc * Bstar := mul_le_mul_of_nonneg_left (hB U hU) hc0
      have hb0 : 0 ≤ cc * Bf U := mul_nonneg hc0 (hB0 U hU)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb0 hb 2)
        (add_nonneg (hPos F U) (hPos G U))
    rw [descendantsAverage_mul_left, descendantsAverage_add] at c1
    exact c1
  have s1 : Real.sqrt (descendantsAverage Q n (fun U => Real.sqrt (X U + Y U) ^ 2)) ≤
      Bstar * Real.sqrt P :=
    calc _ ≤ Real.sqrt (Bstar ^ 2 * P) := Real.sqrt_le_sqrt hA1
      _ = Bstar * Real.sqrt P := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hBs]
  have s2 : Real.sqrt (descendantsAverage Q n (fun U => (cc * Bf U * Real.sqrt
      (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) ^ 2)) ≤
      cc * Bstar * Real.sqrt P :=
    calc _ ≤ Real.sqrt ((cc * Bstar) ^ 2 * P) := Real.sqrt_le_sqrt hA2
      _ = cc * Bstar * Real.sqrt P := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hc0 hBs)]
  have hfin : (Real.sqrt (descendantsAverage Q n (fun U => Real.sqrt (X U + Y U) ^ 2)) +
      Real.sqrt (descendantsAverage Q n (fun U => (cc * Bf U * Real.sqrt
        (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) ^ 2))) ^ 2 ≤
      ((1 + cc) * Bstar) ^ 2 * P := by
    have hsum := add_le_add s1 s2
    have hnn : 0 ≤ Real.sqrt (descendantsAverage Q n (fun U => Real.sqrt (X U + Y U) ^ 2)) +
      Real.sqrt (descendantsAverage Q n (fun U => (cc * Bf U * Real.sqrt
        (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) ^ 2)) := by positivity
    calc _ ≤ (Bstar * Real.sqrt P + cc * Bstar * Real.sqrt P) ^ 2 :=
          pow_le_pow_left₀ hnn hsum 2
      _ = ((1 + cc) * Bstar) ^ 2 * (Real.sqrt P) ^ 2 := by ring
      _ = ((1 + cc) * Bstar) ^ 2 * P := by rw [Real.sq_sqrt hP0]
  have hL : lemmaVTiledWeakEnergy Q n φ.toH1Function.grad +
      lemmaVTiledWeakEnergy Q n η.grad = descendantsAverage Q n (fun U =>
        vectorWeakHaarEnergy U φ.toH1Function.grad + vectorWeakHaarEnergy U η.grad) := by
    unfold lemmaVTiledWeakEnergy
    rw [descendantsAverage_add]
  rw [hL]
  exact h3.trans (h4.trans hfin)

end

end ASDExplicitGamma.Scalar
