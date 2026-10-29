module

public import ASDExplicitGamma.Scalar.PairedTwoSlotZero
public import ASDExplicitGamma.Scalar.PairedTwoSlotParentData

/-! The pure-slot energy bound of the two-slot NEW inverse (constant one). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem twoSlot_energy_sum (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) =
      ⟪s₁, twoSlotY Q hν hσ k s₁ s₂⟫_ℝ +
        ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)),
          (twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
  have h := pair_energy_eq_sum (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂))
  refine h.trans ?_
  rw [Submodule.coe_inner]
  rfl

theorem avg_energy (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ}
    (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q)) :
    (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) =
      (ν / σ) * ((∫ z in openCubeSet Q, vecNormSq (φ.toH1Function.grad z) ∂volume) +
        ∫ z in openCubeSet Q, vecNormSq (η.grad z) ∂volume) := by
  have hx : MemVectorL2 (openCubeSet Q) φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
  have hy : MemVectorL2 (openCubeSet Q) η.grad := η.grad_memVectorL2
  have i1 : IntegrableOn (fun z => vecNormSq (φ.toH1Function.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hx hx
  have i2 : IntegrableOn (fun z => vecNormSq (η.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hy hy
  have hI : IntegrableOn (fun z => (ν / σ) * (vecNormSq (φ.toH1Function.grad z) +
      vecNormSq (η.grad z))) (openCubeSet Q) := (i1.add i2).const_mul (ν / σ)
  refine (integral_eq_vol_mul_avg Q n hI).symm.trans ?_
  rw [integral_const_mul, integral_add i1 i2]

/-- The pure-slot energy bound: when one of the two sources vanishes in the positive
norm on every cell, the pair energy is at most the inverse-history weighted source
energy, with constant one. -/
theorem pure_energy_le (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hGc : ∀ U ∈ descendantsAtDepth Q n, MemLp G 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => G x i))))
    (hM : ∀ U ∈ descendantsAtDepth Q n,
      Real.sqrt (vectorPositiveHaarEnergy U F) * Real.sqrt (vectorPositiveHaarEnergy U G) = 0)
    (s₁ : HilbertVectorL2 (openCubeSet Q)) (s₂ : (physicalPotentialSpace Q).toSubmodule)
    (hs1 : s₁ ∈ (physicalFluxSpace Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ)
    (hs2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ) :
    pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) ≤
      (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) := by
  obtain ⟨φ, η, hc, hd, -, hplus, hnorm⟩ := two_slot_parent_data Q hν hσ k hF hG s₁ s₂
    hs1 hs1' hs2'
  have hsum := two_slot_cell_sum (ε := 1) n hν hσ (by norm_num) k φ η hF hG hc hd hFc hGc
  rw [one_mul, ← hplus] at hsum
  rw [← twoSlot_energy_sum] at hsum
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  have hEn := avg_energy (ν := ν) (σ := σ) Q n φ η
  have hE : pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) =
      (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) := by
    rw [hEn, twoSlot_energy_norm, hnorm]
  have hMzero : descendantsAverage Q n (fun U =>
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        (Real.sqrt (vectorPositiveHaarEnergy U F) *
          Real.sqrt (vectorPositiveHaarEnergy U G))) = 0 := by
    unfold descendantsAverage
    have : ∀ U ∈ descendantsAtDepth Q n, lemmaVInverseHistory U
        (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        (Real.sqrt (vectorPositiveHaarEnergy U F) *
          Real.sqrt (vectorPositiveHaarEnergy U G)) = 0 := fun U hU => by rw [hM U hU, mul_zero]
    simp only [Finset.sum_congr rfl this, Finset.sum_const_zero, mul_zero]
  rw [hMzero, mul_zero, add_zero] at hsum
  set ebar := descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) with hebar
  set W := descendantsAverage Q n (fun U =>
        lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G)) with hW
  have hebar0 : 0 ≤ ebar := by
    have h0 : 0 ≤ pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂)
        (twoSlotX Q hν hσ k s₁ s₂) := by
      rw [twoSlot_energy_norm]
      exact mul_nonneg (div_pos hν hσ).le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [hE] at h0
    exact nonneg_of_mul_nonneg_right h0 hvol
  have hW0 : 0 ≤ W := by
    rw [hW]
    unfold descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro U hU
    exact mul_nonneg (lemmaVInverseHistory_nonneg U _
      (Real.one_lt_rpow (by norm_num) (by norm_num)))
      (add_nonneg (vectorPositiveHaarEnergy_nonneg U F) (vectorPositiveHaarEnergy_nonneg U G))
  have h1 : ebar ≤ Real.sqrt ebar * Real.sqrt W := by
    rw [hE] at hsum
    exact le_of_mul_le_mul_left hsum hvol
  have h2 := le_of_le_sqrt_mul hebar0 hW0 h1
  rw [hE]
  exact mul_le_mul_of_nonneg_left h2 hvol.le

end

end ASDExplicitGamma.Scalar
