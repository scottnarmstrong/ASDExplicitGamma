module

public import ASDExplicitGamma.Scalar.ParentIds
public import ASDExplicitGamma.Scalar.CrossCell
public import ASDExplicitGamma.Scalar.PairedTwoSlotBank

/-! **Pure-source cross bound** (source `sensitivity_pure_source_full_norm_cross` (2.1)): for a pure
first source `s = (Π F, 0)` and an arbitrary paired source `t = (Π Fₜ, Π Gₜ)`, the `J`-pairing of `t`
with the NEW inverse of `s` is at most `1.41 vol √(B* PE(F)) √(B* (PE(Fₜ)+PE(Gₜ)))`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem J_pairing {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (t w : pureFluxPair (Y := Y) (X := X)) :
    ⟪pureFluxParity (Y := Y) (X := X) t, w⟫_ℝ =
      ⟪t.ofLp.1, w.ofLp.1⟫_ℝ - ⟪t.ofLp.2, w.ofLp.2⟫_ℝ := by
  rw [WithLp.prod_inner_apply, pureFluxParity_apply]
  simp [inner_neg_left, sub_eq_add_neg]

/-- The `J`-form of the block inverse is symmetric: `⟨J a, N b⟩ = ⟨J b, N a⟩`. -/
theorem JN_symm {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {α : ℝ} (hα : 0 < α) (B : X →L[ℝ] Y) (a b : pureFluxPair (Y := Y) (X := X)) :
    ⟪pureFluxParity (Y := Y) (X := X) a, pureFluxBlockInverse α hα B b⟫_ℝ =
      ⟪pureFluxParity (Y := Y) (X := X) b, pureFluxBlockInverse α hα B a⟫_ℝ := by
  obtain ⟨a1, a2⟩ := pair_inverse_equations hα B a
  obtain ⟨b1, b2⟩ := pair_inverse_equations hα B b
  rw [J_pairing, J_pairing]
  set ya := (pureFluxBlockInverse α hα B a).ofLp.1
  set xa := (pureFluxBlockInverse α hα B a).ofLp.2
  set yb := (pureFluxBlockInverse α hα B b).ofLp.1
  set xb := (pureFluxBlockInverse α hα B b).ofLp.2
  have e1 : ⟪a.ofLp.1, yb⟫_ℝ = α * ⟪ya, yb⟫_ℝ + ⟪B xa, yb⟫_ℝ := by
    rw [← a1, inner_add_left, real_inner_smul_left]
  have e2 : ⟪a.ofLp.2, xb⟫_ℝ = -⟪B.adjoint ya, xb⟫_ℝ + α * ⟪xa, xb⟫_ℝ := by
    rw [← a2, inner_add_left, inner_neg_left, real_inner_smul_left]
  have f1 : ⟪b.ofLp.1, ya⟫_ℝ = α * ⟪yb, ya⟫_ℝ + ⟪B xb, ya⟫_ℝ := by
    rw [← b1, inner_add_left, real_inner_smul_left]
  have f2 : ⟪b.ofLp.2, xa⟫_ℝ = -⟪B.adjoint yb, xa⟫_ℝ + α * ⟪xb, xa⟫_ℝ := by
    rw [← b2, inner_add_left, inner_neg_left, real_inner_smul_left]
  have g1 : ⟪B xa, yb⟫_ℝ = ⟪xa, B.adjoint yb⟫_ℝ := by
    rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have g2 : ⟪B xb, ya⟫_ℝ = ⟪xb, B.adjoint ya⟫_ℝ := by
    rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  rw [e1, e2, f1, f2, g1, g2, real_inner_comm yb ya, real_inner_comm xb xa,
    real_inner_comm (B.adjoint yb) xa, real_inner_comm (B.adjoint ya) xb, real_inner_comm xb (B.adjoint ya)]
  ring

theorem pure_cross_aux (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F Ft Gt : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hFt : MemVectorL2 (openCubeSet Q) Ft)
    (hGt : MemVectorL2 (openCubeSet Q) Gt)
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hFtc : ∀ U ∈ descendantsAtDepth Q n, MemLp Ft 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => Ft x i))))
    (hGtc : ∀ U ∈ descendantsAtDepth Q n, MemLp Gt 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => Gt x i))))
    (s₁ : HilbertVectorL2 (openCubeSet Q))
    (hs1 : s₁ ∈ (physicalFluxSpace Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ)
    (t₁ : HilbertVectorL2 (openCubeSet Q)) (t₂ : (physicalPotentialSpace Q).toSubmodule)
    (ht1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪t₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hFt, w⟫_ℝ)
    (ht2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(t₂ : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hGt, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ)
    {Bstar : ℝ}
    (hB : ∀ U ∈ descendantsAtDepth Q n, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    ∃ (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q)) (X Y : TriadicCube 2 → ℝ),
      ⟪pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (WithLp.toLp 2 (t₁, t₂)),
      pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
        (physicalProjectedCoefficient Q σ hσ k)
        (WithLp.toLp 2 (s₁, (0 : (physicalPotentialSpace Q).toSubmodule)))⟫_ℝ ≤
        (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
          Real.sqrt (vectorPositiveHaarEnergy U Ft) * Real.sqrt (vectorWeakHaarEnergy U η.grad) +
            Real.sqrt (vectorPositiveHaarEnergy U Gt) *
              Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad)) ∧
      descendantsAverage Q n (fun U => volumeAverage (openCubeSet U) (fun z =>
        (ν / σ) * (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) ≤
      descendantsAverage Q n (fun U => Real.sqrt (vectorPositiveHaarEnergy U F) *
        Real.sqrt (vectorWeakHaarEnergy U η.grad)) ∧
      ∀ U ∈ descendantsAtDepth Q n,
        0 ≤ volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) ∧
        0 ≤ X U ∧ 0 ≤ Y U ∧ X U + Y U ≤ lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          volumeAverage (openCubeSet U) (fun z => (ν / σ) *
            (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) ∧
        Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) ≤ Real.sqrt (X U) +
          (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U
            (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
            Real.sqrt (forcedSourceCircleEnergy U F) ∧
        Real.sqrt (vectorWeakHaarEnergy U η.grad) ≤ Real.sqrt (Y U) := by
  classical
  letI instQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  have hG0 := zeroField_memL2 (openCubeSet Q)
  have hZc : ∀ U ∈ descendantsAtDepth Q n, MemLp zeroField 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) :=
    fun U _ => ⟨zeroField_memLp U, fun i => zeroField_pos U i⟩
  have hZ0 : ∀ w : HilbertVectorL2 (openCubeSet Q),
      ⟪toHilbertVectorL2OfVecField (zeroField_memL2 (openCubeSet Q)), w⟫_ℝ = 0 :=
    fun w => inner_zeroField w
  obtain ⟨φ, η, hc, hd, -, hplus, hnorm, hyK, hyη, hxφ⟩ :=
    two_slot_parent_core_ids Q hν hσ k hF hG0 s₁ (twoSlotY Q hν hσ k s₁ 0)
      0 (twoSlotX Q hν hσ k s₁ 0) hs1 hs1' (fun w => by rw [hZ0]; simp)
      (twoSlot_eq1 Q hν hσ k s₁ 0) (twoSlot_eq2 Q hν hσ k s₁ 0)
  set y0 := twoSlotY Q hν hσ k s₁ 0 with hy0
  set x0 := twoSlotX Q hν hσ k s₁ 0 with hx0
  have hx : MemVectorL2 (openCubeSet Q) φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
  have hy : MemVectorL2 (openCubeSet Q) η.grad := η.grad_memVectorL2
  -- per-cell data
  have hcell : ∀ U ∈ descendantsAtDepth Q n, ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧
      X + Y ≤ lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) ∧
      Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) ≤ Real.sqrt X +
        (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory U
          (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          Real.sqrt (forcedSourceCircleEnergy U F) ∧
      Real.sqrt (vectorWeakHaarEnergy U η.grad) ≤ Real.sqrt Y := by
    intro U hU
    obtain ⟨X, Y, hX, hY, hXY, h1, h2⟩ := two_slot_cell_bound n hν hσ k φ η hG0 hc hd U hU
      (hFc U hU).1 (hFc U hU).2 (hZc U hU).1 (hZc U hU).2
    refine ⟨X, Y, hX, hY, hXY, h1, ?_⟩
    have hcz : forcedSourceCircleEnergy U zeroField ≤ 0 := by
      have := pureFlux_forcedSourceCircleEnergy_le U zeroField
      rw [zeroField_energy] at this
      exact this
    have : Real.sqrt (forcedSourceCircleEnergy U zeroField) = 0 :=
      le_antisymm (by simpa using Real.sqrt_le_sqrt hcz) (Real.sqrt_nonneg _)
    rw [this, mul_zero, add_zero] at h2
    exact h2
  choose! X Y hX hY hXY ha hb using hcell
  have hα : 0 ≤ ν / σ := (div_pos hν hσ).le
  have hint1 : IntegrableOn (fun z => vecDot (F z) (η.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hy
  have e1 : (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) =
      ∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume := by
    have a := avg_energy (ν := ν) (σ := σ) Q n φ η
    have b := twoSlot_energy_norm Q hν hσ k s₁ 0
    have c : pairEnergy' (ν / σ) y0 x0 = ⟪s₁, y0⟫_ℝ +
        ⟪(0 : (physicalPotentialSpace Q).toSubmodule), x0⟫_ℝ :=
      pair_energy_eq_sum (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule) (div_pos hν hσ)
      (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, 0))
    have hp : ⟪s₁, y0⟫_ℝ = ∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume := by
      have hz : (∫ z in openCubeSet Q, vecDot (zeroField z)
          (φ.toH1Function.grad z) ∂volume) = 0 := by simp [zeroField, vecDot]
      have := hplus
      rw [hz] at this
      simpa [inner_zero_left] using this
    rw [a]
    have hn : (ν / σ) * ((∫ z in openCubeSet Q, vecNormSq (φ.toH1Function.grad z) ∂volume) +
        ∫ z in openCubeSet Q, vecNormSq (η.grad z) ∂volume) =
        (ν / σ) * (‖(x0 : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 + ‖y0‖ ^ 2) := by rw [hnorm]
    rw [hn, ← b]
    rw [← hp]
    simpa [inner_zero_left] using c
  have hUsub : ∀ U ∈ descendantsAtDepth Q n, openCubeSet U ⊆ openCubeSet Q :=
    fun U hU => openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hxU : ∀ U ∈ descendantsAtDepth Q n, MemVectorL2 (openCubeSet U) φ.toH1Function.grad :=
    fun U hU => hx.mono_measure (Measure.restrict_mono_set volume (hUsub U hU))
  have hyU : ∀ U ∈ descendantsAtDepth Q n, MemVectorL2 (openCubeSet U) η.grad :=
    fun U hU => hy.mono_measure (Measure.restrict_mono_set volume (hUsub U hU))
  have hB0 : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) := fun U _ =>
    lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hEn : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ volumeAverage (openCubeSet U) (fun z => (ν / σ) *
      (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))) := by
    intro U hU
    unfold volumeAverage
    apply mul_nonneg (by positivity)
    apply integral_nonneg
    intro z
    exact mul_nonneg hα (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))
  -- energy <= duality with the reciprocal output
  have hen_avg : descendantsAverage Q n (fun U => volumeAverage (openCubeSet U) (fun z =>
        (ν / σ) * (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) ≤
      descendantsAverage Q n (fun U => Real.sqrt (vectorPositiveHaarEnergy U F) *
        Real.sqrt (vectorWeakHaarEnergy U η.grad)) := by
    have h1 : (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        volumeAverage (openCubeSet U) (fun z => (ν / σ) *
          (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z)))) ≤
        (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
          Real.sqrt (vectorPositiveHaarEnergy U F) * Real.sqrt (vectorWeakHaarEnergy U η.grad)) := by
      rw [e1, integral_eq_vol_mul_avg Q n hint1]
      apply mul_le_mul_of_nonneg_left _ hvol.le
      apply descendantsAverage_le
      intro U hU
      exact (le_abs_self _).trans (cell_duality U (hFc U hU).1 (hFc U hU).2 (hyU U hU))
    exact le_of_mul_le_mul_left h1 hvol
  -- the cross pairing as cell averages
  have hint2 : IntegrableOn (fun z => vecDot (Ft z) (η.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hFt hy
  have hint3 : IntegrableOn (fun z => vecDot (Gt z) (φ.toH1Function.grad z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hGt hx
  have hcrossEq : ⟪pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (WithLp.toLp 2 (t₁, t₂)),
      pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
        (physicalProjectedCoefficient Q σ hσ k)
        (WithLp.toLp 2 (s₁, (0 : (physicalPotentialSpace Q).toSubmodule)))⟫_ℝ =
      (∫ z in openCubeSet Q, vecDot (Ft z) (η.grad z) ∂volume) -
        ∫ z in openCubeSet Q, vecDot (Gt z) (φ.toH1Function.grad z) ∂volume := by
    rw [J_pairing]
    have a1 := ht1' y0 hyK
    have a2 := ht2' x0
    have e1' : ⟪toHilbertVectorL2OfVecField hFt, y0⟫_ℝ =
        ∫ z in openCubeSet Q, vecDot (Ft z) (η.grad z) ∂volume := by
      rw [hyη, inner_ofField]
    have e2' : ⟪toHilbertVectorL2OfVecField hGt, (x0 : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ∫ z in openCubeSet Q, vecDot (Gt z) (φ.toH1Function.grad z) ∂volume := by
      rw [hxφ, inner_ofField]
    change ⟪t₁, y0⟫_ℝ - ⟪t₂, x0⟫_ℝ = _
    rw [Submodule.coe_inner, a1, a2, e1', e2']
  rw [hcrossEq, integral_eq_vol_mul_avg Q n hint2, integral_eq_vol_mul_avg Q n hint3,
    ← mul_sub, ← descendantsAverage_sub]
  have hcellCross : ∀ U ∈ descendantsAtDepth Q n,
      volumeAverage (openCubeSet U) (fun z => vecDot (Ft z) (η.grad z)) -
        volumeAverage (openCubeSet U) (fun z => vecDot (Gt z) (φ.toH1Function.grad z)) ≤
      Real.sqrt (vectorPositiveHaarEnergy U Ft) * Real.sqrt (vectorWeakHaarEnergy U η.grad) +
        Real.sqrt (vectorPositiveHaarEnergy U Gt) *
          Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad) := by
    intro U hU
    have d1 := cell_duality U (hFtc U hU).1 (hFtc U hU).2 (hyU U hU)
    have d2 := cell_duality U (hGtc U hU).1 (hGtc U hU).2 (hxU U hU)
    have := (le_abs_self _).trans d1
    have := (neg_le_abs _).trans d2
    linarith
  have hstep1 : (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
      volumeAverage (openCubeSet U) (fun z => vecDot (Ft z) (η.grad z)) -
        volumeAverage (openCubeSet U) (fun z => vecDot (Gt z) (φ.toH1Function.grad z))) ≤
      (volume (openCubeSet Q)).toReal * descendantsAverage Q n (fun U =>
        Real.sqrt (vectorPositiveHaarEnergy U Ft) * Real.sqrt (vectorWeakHaarEnergy U η.grad) +
          Real.sqrt (vectorPositiveHaarEnergy U Gt) *
            Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad)) :=
    mul_le_mul_of_nonneg_left (descendantsAverage_le hcellCross) hvol.le
  refine ⟨φ, η, X, Y, hstep1, hen_avg, fun U hU => ⟨hEn U hU, hX U hU, hY U hU, hXY U hU, ha U hU, hb U hU⟩⟩

theorem pure_cross_bound (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F Ft Gt : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hFt : MemVectorL2 (openCubeSet Q) Ft)
    (hGt : MemVectorL2 (openCubeSet Q) Gt)
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hFtc : ∀ U ∈ descendantsAtDepth Q n, MemLp Ft 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => Ft x i))))
    (hGtc : ∀ U ∈ descendantsAtDepth Q n, MemLp Gt 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => Gt x i))))
    (s₁ : HilbertVectorL2 (openCubeSet Q))
    (hs1 : s₁ ∈ (physicalFluxSpace Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ)
    (t₁ : HilbertVectorL2 (openCubeSet Q)) (t₂ : (physicalPotentialSpace Q).toSubmodule)
    (ht1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪t₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hFt, w⟫_ℝ)
    (ht2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(t₂ : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hGt, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ)
    {Bstar : ℝ}
    (hB : ∀ U ∈ descendantsAtDepth Q n, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    ⟪pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (WithLp.toLp 2 (t₁, t₂)),
      pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
        (physicalProjectedCoefficient Q σ hσ k)
        (WithLp.toLp 2 (s₁, (0 : (physicalPotentialSpace Q).toSubmodule)))⟫_ℝ ≤
      (141 / 100 : ℝ) * ((volume (openCubeSet Q)).toReal *
        (Real.sqrt (Bstar * lemmaVTiledPositiveEnergy Q n F) *
          Real.sqrt (Bstar * (lemmaVTiledPositiveEnergy Q n Ft +
            lemmaVTiledPositiveEnergy Q n Gt)))) := by
  classical
  obtain ⟨φ, η, X, Y, hstep1, hen_avg, hcellf⟩ := pure_cross_aux Q n hν hσ k hF hFt hGt hFc hFtc hGtc
    s₁ hs1 hs1' t₁ t₂ ht1' ht2' hB
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  have hB0 : ∀ U ∈ descendantsAtDepth Q n, 0 ≤ lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) := fun U _ =>
    lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  refine hstep1.trans ?_
  -- sum form and the real-variable core
  have hcore := pure_cross_cells (descendantsAtDepth Q n) ((3 : ℝ) ^ (-(1 / 4 : ℝ)))
    (by positivity) (le_of_eq rfl)
    (fun U => lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
      ((3 : ℝ) ^ (1 / 4 : ℝ)))
    (fun U => vectorPositiveHaarEnergy U F) (fun U => forcedSourceCircleEnergy U F)
    (fun U => volumeAverage (openCubeSet U) (fun z => (ν / σ) *
      (vecNormSq (φ.toH1Function.grad z) + vecNormSq (η.grad z))))
    X Y (fun U => Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad))
    (fun U => Real.sqrt (vectorWeakHaarEnergy U η.grad))
    (fun U => vectorPositiveHaarEnergy U Ft) (fun U => vectorPositiveHaarEnergy U Gt)
    hB0 (fun U _ => vectorPositiveHaarEnergy_nonneg U F)
    (fun U _ => ⟨forcedSourceCircleEnergy_nonneg U F, pureFlux_forcedSourceCircleEnergy_le U F⟩)
    (fun U hU => (hcellf U hU).1) (fun U hU => (hcellf U hU).2.1) (fun U hU => (hcellf U hU).2.2.1)
    (fun U hU => (hcellf U hU).2.2.2.1) (fun U _ => Real.sqrt_nonneg _) (fun U _ => Real.sqrt_nonneg _)
    (fun U hU => (hcellf U hU).2.2.2.2.1) (fun U hU => (hcellf U hU).2.2.2.2.2)
    (fun U _ => vectorPositiveHaarEnergy_nonneg U Ft)
    (fun U _ => vectorPositiveHaarEnergy_nonneg U Gt) (by
      have h := hen_avg
      unfold descendantsAverage at h
      rcases Nat.eq_zero_or_pos (descendantsAtDepth Q n).card with h0 | h0
      · rw [Finset.card_eq_zero.1 h0]; simp
      · exact le_of_mul_le_mul_left h (inv_pos.2 (by exact_mod_cast h0)))
  set cinv : ℝ := ((descendantsAtDepth Q n).card : ℝ)⁻¹ with hcinv
  have hc0 : 0 ≤ cinv := by positivity
  set Bf : TriadicCube 2 → ℝ := fun U => lemmaVInverseHistory U
    (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) with hBf
  have hpe : ∀ H : Vec 2 → Vec 2, ∀ U : TriadicCube 2, 0 ≤ vectorPositiveHaarEnergy U H :=
    fun H U => vectorPositiveHaarEnergy_nonneg U H
  have h2 : cinv * ∑ U ∈ descendantsAtDepth Q n, Bf U * vectorPositiveHaarEnergy U F ≤
      Bstar * lemmaVTiledPositiveEnergy Q n F := by
    have : descendantsAverage Q n (fun U => Bf U * vectorPositiveHaarEnergy U F) ≤
        descendantsAverage Q n (fun U => Bstar * vectorPositiveHaarEnergy U F) :=
      descendantsAverage_le fun U hU => mul_le_mul_of_nonneg_right (hB U hU) (hpe F U)
    rw [descendantsAverage_mul_left] at this
    exact this
  have h3 : cinv * ∑ U ∈ descendantsAtDepth Q n, Bf U * (vectorPositiveHaarEnergy U Ft +
      vectorPositiveHaarEnergy U Gt) ≤
      Bstar * (lemmaVTiledPositiveEnergy Q n Ft + lemmaVTiledPositiveEnergy Q n Gt) := by
    have : descendantsAverage Q n (fun U => Bf U * (vectorPositiveHaarEnergy U Ft +
        vectorPositiveHaarEnergy U Gt)) ≤
        descendantsAverage Q n (fun U => Bstar * (vectorPositiveHaarEnergy U Ft +
          vectorPositiveHaarEnergy U Gt)) :=
      descendantsAverage_le fun U hU => mul_le_mul_of_nonneg_right (hB U hU)
        (add_nonneg (hpe Ft U) (hpe Gt U))
    rw [descendantsAverage_mul_left, descendantsAverage_add] at this
    exact this
  have h1 : descendantsAverage Q n (fun U =>
      Real.sqrt (vectorPositiveHaarEnergy U Ft) * Real.sqrt (vectorWeakHaarEnergy U η.grad) +
        Real.sqrt (vectorPositiveHaarEnergy U Gt) *
          Real.sqrt (vectorWeakHaarEnergy U φ.toH1Function.grad)) ≤
      (141 / 100 : ℝ) * (Real.sqrt (cinv * ∑ U ∈ descendantsAtDepth Q n,
          Bf U * vectorPositiveHaarEnergy U F) *
        Real.sqrt (cinv * ∑ U ∈ descendantsAtDepth Q n, Bf U * (vectorPositiveHaarEnergy U Ft +
          vectorPositiveHaarEnergy U Gt))) := by
    have hcc : Real.sqrt cinv * Real.sqrt cinv = cinv := Real.mul_self_sqrt hc0
    rw [Real.sqrt_mul hc0, Real.sqrt_mul hc0]
    calc descendantsAverage Q n (fun U => _) = cinv * ∑ U ∈ descendantsAtDepth Q n, _ := rfl
      _ ≤ cinv * ((141 / 100 : ℝ) * Real.sqrt (∑ U ∈ descendantsAtDepth Q n, Bf U *
            vectorPositiveHaarEnergy U F) * Real.sqrt (∑ U ∈ descendantsAtDepth Q n, Bf U *
              (vectorPositiveHaarEnergy U Ft + vectorPositiveHaarEnergy U Gt))) :=
          mul_le_mul_of_nonneg_left hcore hc0
      _ = _ := by
        generalize Real.sqrt (∑ U ∈ descendantsAtDepth Q n, Bf U *
          vectorPositiveHaarEnergy U F) = u
        generalize Real.sqrt (∑ U ∈ descendantsAtDepth Q n, Bf U *
          (vectorPositiveHaarEnergy U Ft + vectorPositiveHaarEnergy U Gt)) = w
        generalize Real.sqrt cinv = sc at hcc ⊢
        linear_combination (-((141 / 100 : ℝ) * u * w)) * hcc
  have h4 := mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h2) (Real.sqrt_le_sqrt h3)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by norm_num : (0 : ℝ) ≤ 141 / 100)
  calc (volume (openCubeSet Q)).toReal * _ ≤ (volume (openCubeSet Q)).toReal * _ :=
        mul_le_mul_of_nonneg_left (h1.trans h4) hvol.le
    _ = _ := by ring

end

end ASDExplicitGamma.Scalar
