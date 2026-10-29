module

public import ASDExplicitGamma.Scalar.PairedTwoSlotDuality

/-! The cell sum of the two-slot bound for a function-level solution. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Inverse

noncomputable section

theorem descendantsAverage_sub (Q : TriadicCube 2) (n : ℕ) (A B : TriadicCube 2 → ℝ) :
    descendantsAverage Q n (fun U => A U - B U) =
      descendantsAverage Q n A - descendantsAverage Q n B := by
  change ((descendantsAtDepth Q n).card : ℝ)⁻¹ * ∑ U ∈ descendantsAtDepth Q n, (A U - B U) =
    ((descendantsAtDepth Q n).card : ℝ)⁻¹ * (descendantsAtDepth Q n).sum A -
      ((descendantsAtDepth Q n).card : ℝ)⁻¹ * (descendantsAtDepth Q n).sum B
  rw [Finset.sum_sub_distrib]
  ring

theorem two_slot_cell_sum {Q : TriadicCube 2} (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    {ε : ℝ} (hε : |ε| ≤ 1)
    (k : ResponseCoefficient (openCubeSet Q))
    (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q))
    {F G : Vec 2 → Vec 2}
    (hFQ : MemVectorL2 (openCubeSet Q) F) (hGQ : MemVectorL2 (openCubeSet Q) G)
    (hc : IsSolenoidalOn (openCubeSet Q) (fun z =>
      (ν / σ) • η.grad z + shear' σ k z (φ.toH1Function.grad z) - F z))
    (hd : IsSolenoidalOn (openCubeSet Q) (fun z =>
      (ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z) - G z))
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hGc : ∀ U ∈ descendantsAtDepth Q n, MemLp G 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => G x i)))) :
    (∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume) +
        ε * ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume ≤
      (volume (openCubeSet Q)).toReal *
        (Real.sqrt (descendantsAverage Q n (fun U => volumeAverage (openCubeSet U)
            (fun z => (ν / σ) * (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))))) *
          Real.sqrt (descendantsAverage Q n (fun U =>
            lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
              ((3 : ℝ) ^ (1 / 4 : ℝ)) *
              (vectorPositiveHaarEnergy U F + vectorPositiveHaarEnergy U G))) +
        2 * (3 : ℝ) ^ (-(1 / 4 : ℝ)) * descendantsAverage Q n (fun U =>
          lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
              ((3 : ℝ) ^ (1 / 4 : ℝ)) *
            (Real.sqrt (vectorPositiveHaarEnergy U F) *
              Real.sqrt (vectorPositiveHaarEnergy U G)))) := by
  letI instQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hx : MemVectorL2 (openCubeSet Q) φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
  have hy : MemVectorL2 (openCubeSet Q) η.grad := η.grad_memVectorL2
  have hcell : ∀ U ∈ descendantsAtDepth Q n, ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧
      X + Y ≤ lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) ∧
      Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) ≤ Real.sqrt X +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          Real.sqrt (forcedSourceCircleEnergy U F) ∧
      Real.sqrt (vectorWeakHaarEnergy U η.grad) ≤ Real.sqrt Y +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          Real.sqrt (forcedSourceCircleEnergy U G) :=
    fun U hU => two_slot_cell_bound n hν hσ k φ η hGQ hc hd U hU (hFc U hU).1
      (hFc U hU).2 (hGc U hU).1 (hGc U hU).2
  choose! X Y hX hY hXY h1 h2 using hcell
  have hint1 : IntegrableOn (fun z => vecDot (F z) (η.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hFQ hy
  have hint2 : IntegrableOn (fun z => vecDot (G z) (φ.toH1Function.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hGQ hx
  rw [integral_eq_vol_mul_avg Q n hint1, integral_eq_vol_mul_avg Q n hint2]
  have hcomb : (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => vecDot (F z) (η.grad z))) +
      ε * ((volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => vecDot (G z) (φ.toH1Function.grad z)))) =
      (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => vecDot (F z) (η.grad z)) +
        ε * volumeAverage (openCubeSet U) (fun z => vecDot (G z) (φ.toH1Function.grad z))) := by
    rw [descendantsAverage_add, descendantsAverage_mul_left]
    ring
  rw [hcomb]
  have hvol : 0 ≤ (volume (openCubeSet Q)).toReal := ENNReal.toReal_nonneg
  apply mul_le_mul_of_nonneg_left _ hvol
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hBn : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) := fun U hU =>
    lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hEn : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ volumeAverage (openCubeSet U) (fun z => (ν / σ) *
      (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) := by
    intro U hU
    unfold volumeAverage
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro z
    have hα : 0 ≤ ν / σ := (div_pos hν hσ).le
    exact mul_nonneg hα (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))
  have ht : ∀ U ∈ descendantsAtDepth Q n,
      (volumeAverage (openCubeSet U) (fun z => vecDot (F z) (η.grad z)) +
        ε * volumeAverage (openCubeSet U) (fun z => vecDot (G z) (φ.toH1Function.grad z))) ≤
      Real.sqrt (Y U) * Real.sqrt (vectorPositiveHaarEnergy U F) +
        Real.sqrt (X U) * Real.sqrt (vectorPositiveHaarEnergy U G) +
        2 * (3 : ℝ) ^ (-(1 / 4 : ℝ)) * (lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          (Real.sqrt (vectorPositiveHaarEnergy U F) *
            Real.sqrt (vectorPositiveHaarEnergy U G))) := by
    intro U hU
    have hUQ : openCubeSet U ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hU
    have hsub : Measure.restrict volume (openCubeSet U) ≤ Measure.restrict volume (openCubeSet Q) :=
      Measure.restrict_mono_set volume hUQ
    have hxU : MemVectorL2 (openCubeSet U) φ.toH1Function.grad := hx.mono_measure hsub
    have hyU : MemVectorL2 (openCubeSet U) η.grad := hy.mono_measure hsub
    have d1 := cell_duality U (hFc U hU).1 (hFc U hU).2 hyU
    have d2 := cell_duality U (hGc U hU).1 (hGc U hU).2 hxU
    have cF : Real.sqrt (forcedSourceCircleEnergy U F) ≤ Real.sqrt (vectorPositiveHaarEnergy U F) :=
      Real.sqrt_le_sqrt (pureFlux_forcedSourceCircleEnergy_le U F)
    have cG : Real.sqrt (forcedSourceCircleEnergy U G) ≤ Real.sqrt (vectorPositiveHaarEnergy U G) :=
      Real.sqrt_le_sqrt (pureFlux_forcedSourceCircleEnergy_le U G)
    have hB0 := hBn U hU
    have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
    have pF0 := Real.sqrt_nonneg (vectorPositiveHaarEnergy U F)
    have pG0 := Real.sqrt_nonneg (vectorPositiveHaarEnergy U G)
    have wY := h2 U hU
    have wX := h1 U hU
    have w1 : Real.sqrt (vectorWeakHaarEnergy U η.grad) ≤ Real.sqrt (Y U) +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          Real.sqrt (vectorPositiveHaarEnergy U G) := by
      refine wY.trans (add_le_add le_rfl ?_)
      exact mul_le_mul_of_nonneg_left cG (mul_nonneg hc0 hB0)
    have w2 : Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) ≤ Real.sqrt (X U) +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          Real.sqrt (vectorPositiveHaarEnergy U F) := by
      refine wX.trans (add_le_add le_rfl ?_)
      exact mul_le_mul_of_nonneg_left cF (mul_nonneg hc0 hB0)
    have a1 := (le_abs_self _).trans d1
    have a2 : ε * volumeAverage (openCubeSet U) (fun z => vecDot (G z) (φ.toH1Function.grad z)) ≤
        Real.sqrt (vectorPositiveHaarEnergy U G) *
          Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hε).trans d2
    have b1 := mul_le_mul_of_nonneg_left w1 pF0
    have b2 := mul_le_mul_of_nonneg_left w2 pG0
    nlinarith [a1, a2, b1, b2]
  have key := cell_aggregation Q n _ X Y
    (fun U => lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
      ((3 : ℝ) ^ (1 / 4 : ℝ)))
    (fun U => volumeAverage (openCubeSet U) (fun z => (ν / σ) *
      (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))))
    (fun U => Real.sqrt (vectorPositiveHaarEnergy U F))
    (fun U => Real.sqrt (vectorPositiveHaarEnergy U G)) hc0 hX hY hBn hEn
    (fun U hU => Real.sqrt_nonneg _) (fun U hU => Real.sqrt_nonneg _) hXY ht
  have hsqF : ∀ U : TriadicCube 2, Real.sqrt (vectorPositiveHaarEnergy U F) ^ 2 =
      vectorPositiveHaarEnergy U F := fun U => Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U F)
  have hsqG : ∀ U : TriadicCube 2, Real.sqrt (vectorPositiveHaarEnergy U G) ^ 2 =
      vectorPositiveHaarEnergy U G := fun U => Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U G)
  simp only [hsqF, hsqG] at key
  exact key

end

end ASDExplicitGamma.Scalar
