module

public import ASDExplicitGamma.Scalar.RefQuart
public import ASDExplicitGamma.Scalar.PairedTwoSlotBank

/-! Pathwise bounds of the flat leg `a = σ⁻² (Π F_flat, 0)` at the big cube, depth 134. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem inner_smul2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ℝ)
    (u v : E) : ⟪c • u, c • v⟫_ℝ = c * c * ⟪u, v⟫_ℝ := by
  rw [real_inner_smul_left, real_inner_smul_right]; ring

namespace Cfg''

section Flat

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- Admissibility of the flat field on cells of depth 134 (the cell data of the flat leg). -/
def FlatCellAdm (ω : Cutoff.CutoffSample 2) : Prop :=
  ∀ U ∈ descendantsAtDepth (originCube 2 (m + 129)) 134,
    MemLp (flatField (originCube 2 (m + 129)) hab hcd e m ω) 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1)
          (fun x => flatField (originCube 2 (m + 129)) hab hcd e m ω x i)))

include hQ in
theorem flatField_memL2 (ω : Cutoff.CutoffSample 2) :
    MemVectorL2 (openCubeSet (originCube 2 (m + 129)))
      (flatField (originCube 2 (m + 129)) hab hcd e m ω) :=
  memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure _
    (flat_source_q3_actual_rotated_wick_admissible
      (originCube 2 (m + 129)) hab hcd hQ e m ω).1

/-- The pure flat leg has diagonal at most `σ⁻⁴ vol B* PE(F_flat)` (energy bound with constant one). -/
theorem aR_diag_le (ω : Cutoff.CutoffSample 2) (hadm : FlatCellAdm m hab hcd e ω) :
    ⟪(CC).Jop ((CC).aR m ω), (CC).Nop m ω ((CC).aR m ω)⟫_ℝ ≤
      ((((CC).σ ^ 2)⁻¹ : ℝ) ^ 2) * ((volume (openCubeSet (originCube 2 (m + 129)))).toReal *
        (bnew M m (originCube 2 (m + 129)) ω *
          lemmaVTiledPositiveEnergy (originCube 2 (m + 129)) 134
            (flatField (originCube 2 (m + 129)) hab hcd e m ω))) := by
  classical
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  have hF := flatField_memL2 m hab hcd hQ e ω
  set Fl := flatField (originCube 2 (m + 129)) hab hcd e m ω with hFl
  have hvol : 0 ≤ (volume (openCubeSet (originCube 2 (m + 129)))).toReal := ENNReal.toReal_nonneg
  have hG0 := zeroField_memL2 (openCubeSet (originCube 2 (m + 129)))
  have hZc : ∀ U ∈ descendantsAtDepth (originCube 2 (m + 129)) 134,
      MemLp zeroField 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) :=
    fun U _ => ⟨zeroField_memLp U, fun i => zeroField_pos U i⟩
  have hZ0 : ∀ w : HilbertVectorL2 (openCubeSet (originCube 2 (m + 129))),
      ⟪toHilbertVectorL2OfVecField (zeroField_memL2 (openCubeSet (originCube 2 (m + 129)))), w⟫_ℝ = 0 :=
    fun w => inner_zeroField w
  have hpure := pure_energy_le (originCube 2 (m + 129)) 134 (CC).hν (CC).hσ
    ((CC).Rest (modelInsertedScalar (CC).K m 1 ω)) hF hG0 hadm hZc
    (fun U _ => by rw [zeroField_energy]; simp)
    (fluxSource (originCube 2 (m + 129)) hF) 0 (fluxSource_mem _ hF)
    (fluxSource_inner _ hF) (fun w => by rw [hZ0]; simp)
  have hBn := Bnew_cell_bound M ell m (originCube 2 (m + 129)) ω (CC).K (CC).hQcl hK
  set k := (CC).Rest (modelInsertedScalar (CC).K m 1 ω) with hk
  set s₁ := fluxSource (originCube 2 (m + 129)) hF with hs₁
  have hJN : ⟪(CC).Jop (WithLp.toLp 2 (s₁, (0 : (CC).Xs)) : (CC).Pr),
      (CC).Nop m ω (WithLp.toLp 2 (s₁, (0 : (CC).Xs)) : (CC).Pr)⟫_ℝ =
      pairEnergy' ((CC).ν / (CC).σ) (twoSlotY _ (CC).hν (CC).hσ k s₁ 0)
        (twoSlotX _ (CC).hν (CC).hσ k s₁ 0) := by
    have e0 : pairEnergy' ((CC).ν / (CC).σ) (twoSlotY _ (CC).hν (CC).hσ k s₁ 0)
        (twoSlotX _ (CC).hν (CC).hσ k s₁ 0) = ⟪s₁, twoSlotY _ (CC).hν (CC).hσ k s₁ 0⟫_ℝ +
        ⟪(0 : (physicalPotentialSpace (originCube 2 (m + 129))).toSubmodule),
          twoSlotX _ (CC).hν (CC).hσ k s₁ 0⟫_ℝ :=
      pair_energy_eq_sum (Y := HilbertVectorL2 (openCubeSet (originCube 2 (m + 129))))
        (X := (physicalPotentialSpace (originCube 2 (m + 129))).toSubmodule)
        (div_pos (CC).hν (CC).hσ)
        (physicalProjectedCoefficient (originCube 2 (m + 129)) (CC).σ (CC).hσ k)
        (WithLp.toLp 2 (s₁, 0))
    have e1 : ⟪(CC).Jop (WithLp.toLp 2 (s₁, (0 : (CC).Xs)) : (CC).Pr),
        (CC).Nop m ω (WithLp.toLp 2 (s₁, (0 : (CC).Xs)) : (CC).Pr)⟫_ℝ =
        ⟪s₁, twoSlotY _ (CC).hν (CC).hσ k s₁ 0⟫_ℝ -
          ⟪(0 : (physicalPotentialSpace (originCube 2 (m + 129))).toSubmodule),
            twoSlotX _ (CC).hν (CC).hσ k s₁ 0⟫_ℝ := by
      rw [Cfg''.Jop, J_pairing, (CC).Nop_eq]
      rfl
    rw [e0, e1]; simp
  have hbound : pairEnergy' ((CC).ν / (CC).σ) (twoSlotY _ (CC).hν (CC).hσ k s₁ 0)
        (twoSlotX _ (CC).hν (CC).hσ k s₁ 0) ≤ (volume (openCubeSet (originCube 2 (m + 129)))).toReal *
        (bnew M m (originCube 2 (m + 129)) ω * lemmaVTiledPositiveEnergy (originCube 2 (m + 129)) 134 Fl) := by
    refine hpure.trans (mul_le_mul_of_nonneg_left ?_ hvol)
    have h2 : descendantsAverage (originCube 2 (m + 129)) 134 (fun U =>
        lemmaVInverseHistory U (responseFramePlanarCoefficientField (CC).ν (CC).σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) * (vectorPositiveHaarEnergy U Fl + vectorPositiveHaarEnergy U zeroField)) ≤
        descendantsAverage (originCube 2 (m + 129)) 134 (fun U =>
          bnew M m (originCube 2 (m + 129)) ω * vectorPositiveHaarEnergy U Fl) :=
      descendantsAverage_le fun U hU => by
        rw [zeroField_energy, add_zero]
        exact mul_le_mul_of_nonneg_right (hBn U hU) (vectorPositiveHaarEnergy_nonneg U _)
    rw [descendantsAverage_mul_left] at h2
    exact h2
  have haR : (CC).aR m ω = (((CC).σ ^ 2)⁻¹ : ℝ) • (WithLp.toLp 2 (s₁, (0 : (CC).Xs)) : (CC).Pr) :=
    aR_eq M h m hab hcd hQ e ω
  rw [haR]
  simp only [map_smul]
  rw [show ∀ (c : ℝ) (u v : (CC).Pr), ⟪c • u, c • v⟫_ℝ = c * c * ⟪u, v⟫_ℝ from
    fun c u v => inner_smul2 c u v, hJN]
  have hc0 : 0 ≤ (((CC).σ ^ 2)⁻¹ : ℝ) := inv_nonneg.2 (sq_nonneg _)
  calc (((CC).σ ^ 2)⁻¹ : ℝ) * (((CC).σ ^ 2)⁻¹ : ℝ) * _ =
      ((((CC).σ ^ 2)⁻¹ : ℝ) ^ 2) * _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

end Flat

end Cfg''

end

end ASDExplicitGamma.Scalar
