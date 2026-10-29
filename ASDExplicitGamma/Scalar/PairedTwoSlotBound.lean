module

public import ASDExplicitGamma.Scalar.PairedTwoSlotEnergy

/-! The paired two-slot NEW-inverse bound with constant `44/25`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance boundFinite (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The flux component `Π_flux F` of a source field. -/
def fluxSource (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) : HilbertVectorL2 (openCubeSet Q) :=
  (physicalFluxSpace Q).toSubmodule.subtypeL
    ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
      (toHilbertVectorL2OfVecField hF))

/-- The potential component `Π_X G` of a source field. -/
def potSource (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : MemVectorL2 (openCubeSet Q) G) : (physicalPotentialSpace Q).toSubmodule :=
  (physicalPotentialSpace Q).toSubmodule.orthogonalProjectionOnto
    (toHilbertVectorL2OfVecField hG)

theorem fluxSource_mem (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    fluxSource Q hF ∈ (physicalFluxSpace Q).toSubmodule :=
  ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto _).2

theorem fluxSource_inner (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪fluxSource Q hF, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ := by
  intro w hw
  change ⟪(physicalFluxSpace Q).toSubmodule.starProjection (toHilbertVectorL2OfVecField hF),
    w⟫_ℝ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).2 hw]

theorem potSource_inner (Q : TriadicCube 2) {G : Vec 2 → Vec 2}
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(potSource Q hG : HilbertVectorL2 (openCubeSet Q)),
        (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
  intro w
  change ⟪(physicalPotentialSpace Q).toSubmodule.starProjection
      (toHilbertVectorL2OfVecField hG), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).2 w.2]

theorem avg_two_mul_le (Q : TriadicCube 2) (n : ℕ) (B a b : TriadicCube 2 → ℝ)
    (hB : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ B U)
    (ha : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ a U) (hb : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ b U) :
    2 * descendantsAverage Q n (fun U => B U * (Real.sqrt (a U) * Real.sqrt (b U))) ≤
      descendantsAverage Q n (fun U => B U * (a U + b U)) := by
  rw [← descendantsAverage_mul_left]
  apply descendantsAverage_le
  intro U hU
  have h1 := Real.sq_sqrt (ha U hU)
  have h2 := Real.sq_sqrt (hb U hU)
  have h3 : 2 * (Real.sqrt (a U) * Real.sqrt (b U)) ≤ a U + b U := by
    nlinarith [sq_nonneg (Real.sqrt (a U) - Real.sqrt (b U))]
  calc 2 * (B U * (Real.sqrt (a U) * Real.sqrt (b U))) =
        B U * (2 * (Real.sqrt (a U) * Real.sqrt (b U))) := by ring
    _ ≤ B U * (a U + b U) := mul_le_mul_of_nonneg_left h3 (hB U hU)

/-- The paired two-slot bound in terms of the slot components `(s₁, s₂)`. -/
theorem two_slot_bound_core (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
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
    {Bstar : ℝ}
    (hB : ∀ U ∈ descendantsAtDepth Q n, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    ⟪s₁, twoSlotY Q hν hσ k s₁ s₂⟫_ℝ -
        ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)),
          (twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))⟫_ℝ ≤
      (44 / 25 : ℝ) * ((volume (openCubeSet Q)).toReal *
        (Bstar * (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G))) := by
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  have hz1 : (0 : HilbertVectorL2 (openCubeSet Q)) ∈ (physicalFluxSpace Q).toSubmodule :=
    Submodule.zero_mem _
  have hZc : ∀ U ∈ descendantsAtDepth Q n, MemLp zeroField 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) :=
    fun U _ => ⟨zeroField_memLp U, fun i => zeroField_pos U i⟩
  have hZ0 : ∀ w : HilbertVectorL2 (openCubeSet Q),
      ⟪toHilbertVectorL2OfVecField (zeroField_memL2 (openCubeSet Q)), w⟫_ℝ = 0 :=
    fun w => inner_zeroField w
  -- pure first slot
  have hP1 := pure_energy_le Q n hν hσ k hF (zeroField_memL2 (openCubeSet Q)) hFc hZc
    (fun U _ => by rw [zeroField_energy]; simp) s₁ 0 hs1 hs1'
    (fun w => by rw [hZ0]; simp)
  -- pure second slot
  have hP2 := pure_energy_le Q n hν hσ k (zeroField_memL2 (openCubeSet Q)) hG hZc hGc
    (fun U _ => by rw [zeroField_energy]; simp) 0 s₂ hz1
    (fun w _ => by rw [hZ0]; simp) hs2'
  -- the full problem
  obtain ⟨φ, η, hc, hd, hid, -, hnorm⟩ := two_slot_parent_data Q hν hσ k hF hG s₁ s₂
    hs1 hs1' hs2'
  have hsum := two_slot_cell_sum (ε := -1) n hν hσ (by norm_num) k φ η hF hG hc hd hFc hGc
  rw [neg_one_mul, ← sub_eq_add_neg, ← hid] at hsum
  have hEn := avg_energy (ν := ν) (σ := σ) Q n φ η
  have hE : pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) =
      (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) := by
    rw [hEn, twoSlot_energy_norm, hnorm]
  rw [twoSlot_energy_split] at hE
  set ebar := descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) with hebar
  set Bf : TriadicCube 2 → ℝ := fun U => lemmaVInverseHistory U
    (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) with hBf
  have hB0 : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ Bf U := fun U _ =>
    lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hPos : ∀ (H : Vec 2 → Vec 2) (U : TriadicCube 2), 0 ≤ vectorPositiveHaarEnergy U H :=
    fun H U => vectorPositiveHaarEnergy_nonneg U H
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
  have hebar0 : 0 ≤ ebar := by
    have h0 : 0 ≤ (volume (openCubeSet Q)).toReal * ebar := by
      rw [← hE]
      exact add_nonneg
        (by rw [twoSlot_energy_norm]
            exact mul_nonneg (div_pos hν hσ).le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
        (by rw [twoSlot_energy_norm]
            exact mul_nonneg (div_pos hν hσ).le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact nonneg_of_mul_nonneg_right h0 hvol
  have hW0 : 0 ≤ W := by
    rw [hW]
    unfold descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro U hU
    exact mul_nonneg (hB0 U hU) (add_nonneg (hPos F U) (hPos G U))
  have hsq : Real.sqrt ebar * Real.sqrt W ≤ W := by
    calc Real.sqrt ebar * Real.sqrt W ≤ Real.sqrt W * Real.sqrt W :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hebarW) (Real.sqrt_nonneg _)
      _ = W := Real.mul_self_sqrt hW0
  have hM2 := avg_two_mul_le Q n Bf (fun U => vectorPositiveHaarEnergy U F)
    (fun U => vectorPositiveHaarEnergy U G) hB0 (fun U _ => hPos F U) (fun U _ => hPos G U)
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hcle := three_pow_neg_quarter_le
  have hWB : W ≤ Bstar * (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G) := by
    have h1 : W ≤ descendantsAverage Q n (fun U => Bstar * (vectorPositiveHaarEnergy U F +
        vectorPositiveHaarEnergy U G)) := by
      rw [hW]
      apply descendantsAverage_le
      intro U hU
      exact mul_le_mul_of_nonneg_right (hB U hU) (add_nonneg (hPos F U) (hPos G U))
    rw [descendantsAverage_mul_left, descendantsAverage_add] at h1
    exact h1
  have hq := hsum
  have hfin : (volume (openCubeSet Q)).toReal *
      (Real.sqrt ebar * Real.sqrt W + 2 * (3 : ℝ) ^ (-(1 / 4 : ℝ)) *
        descendantsAverage Q n (fun U => Bf U * (Real.sqrt (vectorPositiveHaarEnergy U F) *
          Real.sqrt (vectorPositiveHaarEnergy U G)))) ≤
      (44 / 25 : ℝ) * ((volume (openCubeSet Q)).toReal *
        (Bstar * (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G))) := by
    have hcM : 2 * (3 : ℝ) ^ (-(1 / 4 : ℝ)) *
        descendantsAverage Q n (fun U => Bf U * (Real.sqrt (vectorPositiveHaarEnergy U F) *
          Real.sqrt (vectorPositiveHaarEnergy U G))) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) * W := by
      have := mul_le_mul_of_nonneg_left hM2 hc0
      linarith
    have h3 : Real.sqrt ebar * Real.sqrt W + 2 * (3 : ℝ) ^ (-(1 / 4 : ℝ)) *
        descendantsAverage Q n (fun U => Bf U * (Real.sqrt (vectorPositiveHaarEnergy U F) *
          Real.sqrt (vectorPositiveHaarEnergy U G))) ≤ (44 / 25 : ℝ) *
          (Bstar * (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G)) := by
      nlinarith [mul_le_mul_of_nonneg_left hWB (by norm_num : (0 : ℝ) ≤ 44 / 25)]
    nlinarith [mul_le_mul_of_nonneg_left h3 hvol.le]
  exact hq.trans hfin

end

end ASDExplicitGamma.Scalar
