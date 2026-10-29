module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBound
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometry
import ASDExplicitGamma.Native.VanishingBracketOverlap

/-! The common-shell Riesz average pays the physical overlap factor and the
sharp profile already proved for each actual refined child. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace Topology

/-- The common-shell average of the actual child-observation Riesz vectors is
bounded by the refined-grid overlap factor times the normalized average of
the child-scale SHEAR profiles. -/
theorem nativeHeatQ3RefinedCarrierMeanRieszAverage_sq_le_profiles
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let s : ℕ := d.val + 2
    let amp := q3ModelAmplitude M h (m + (s : ℤ))
    let L := q3ModelLength (m + (s : ℤ))
    let ρ := cubeScaleFactor (originCube 2 m) / L.1
    let δ := diagMeshRadius (originCube 2 m)
      (pureFluxBankSourceDepth s) / L.1
    let profile : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
      let Q := nativeHeatQ3RefinedCarrierChild m i
      let A := nativeHeat_translateTriadicFieldToOrigin Q
      let B := lemmaVTileHistory (originCube 2 Q.scale)
        (pureFluxBankSourceDepth s)
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction Q.scale (A (x i))))
      let T := modelTraceObservable Q.scale M.nu σ (A (x i))
      B ^ 2 * T * (T + 4)
    ‖((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹) •
      ∑ i : nativeHeatQ3RefinedCarrierIndex,
        (InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
            (q3RemainderValueFactor
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
                cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
                cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
              amp L
              ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
                nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
                  (subset_closure
                    (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                      (nativeHeatQ3RefinedCarrierChild m i)))⟩))‖ ^ 2 ≤
      4 * (amp ^ 2 / σ ^ 2) * q3GridOverlapFactor 10 s *
        (lemmaVH2Bn ρ δ) ^ 2 *
        ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i, profile i) := by
  classical
  dsimp only
  let I := Fin (3 ^ 10) × Fin (3 ^ 10)
  let C := nativeHeatQ3RefinedCarrierIndex
  let e : I ≃ C := finProdFinEquiv
  let s : ℕ := d.val + 2
  let amp := q3ModelAmplitude M h (m + (s : ℤ))
  let L := q3ModelLength (m + (s : ℤ))
  let ρ := cubeScaleFactor (originCube 2 m) / L.1
  let δ := diagMeshRadius (originCube 2 m)
    (pureFluxBankSourceDepth s) / L.1
  let profile : C → ℝ := fun i =>
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let B := lemmaVTileHistory (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ
        (pureFluxOpenResponseRestriction Q.scale (A (x i))))
    let T := modelTraceObservable Q.scale M.nu σ (A (x i))
    B ^ 2 * T * (T + 4)
  let parent := originCube 2 (m + 10)
  let a₀ : I → ℝ := fun ij =>
    cubeCorner (nativeHeatQ3RefinedCarrierChild m (e ij)) 0
  let a₁ : I → ℝ := fun ij =>
    a₀ ij + cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m (e ij))
  let b₀ : I → ℝ := fun ij =>
    cubeCorner (nativeHeatQ3RefinedCarrierChild m (e ij)) 1
  let b₁ : I → ℝ := fun ij =>
    b₀ ij + cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m (e ij))
  let Lfun : I → {l : ℝ // 0 < l} := fun _ => L
  let β : I → ℝ := fun _ => amp
  let center : ∀ ij : I, closedRectangle (a₀ ij) (a₁ ij) (b₀ ij) (b₁ ij) :=
    fun ij => ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m (e ij)), by
      simpa [a₀, a₁, b₀, b₁, nativeHeatQ3RefinedCarrierChildRectangle] using
        nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m (e ij)
          (subset_closure
            (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
              (nativeHeatQ3RefinedCarrierChild m (e ij))))⟩
  let O : ∀ ij : I, C(closedRectangle (a₀ ij) (a₁ ij) (b₀ ij) (b₁ ij), ℝ) →L[ℝ] ℝ :=
    fun ij => nativeHeatQ3RefinedChildMeanTraceObservation M σ m x (e ij)
  let factor : ∀ ij : I, WhiteNoise →L[ℝ]
      C(closedRectangle (a₀ ij) (a₁ ij) (b₀ ij) (b₁ ij), ℝ) :=
    fun ij => q3RemainderValueFactor (a₀ ij) (a₁ ij) (b₀ ij) (b₁ ij)
      (β ij) (Lfun ij) (center ij)
  let S : Finset I := Finset.univ
  let N : ℝ := Fintype.card I
  let C₀ : ℝ := q3GridOverlapFactor 10 s * N
  let active : Vec 2 → Finset I := nativeHeatQ3RefinedGridActiveFinset parent L
  let U : Vec 2 → Finset I := active
  have hscale (ij : I) :
      (nativeHeatQ3RefinedCarrierChild m (e ij)).scale = m :=
    nativeHeatQ3RefinedCarrierChild_scale m (e ij)
  have hsLower : 1 ≤ s := by dsimp [s]; omega
  have hsUpper : s ≤ 10 := by dsimp [s]; omega
  have hL : L.1 / cubeScaleFactor parent = (q3GridKernelScale 10 s).1 := by
    change (3 : ℝ) ^ (m + (s : ℤ)) / (3 : ℝ) ^ (m + 10) = _
    rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [show m + (s : ℤ) - (m + 10 : ℤ) = (s : ℤ) - 10 by omega]
    exact (nativeHeat_q3GridKernelScale_eq_zpow_any 10 s).symm
  have hchild (ij : I) :
      nativeHeatQ3RefinedCarrierChild m (e ij) =
        nativeHeatQ3RefinedChildCube parent ij := by
    simp only [nativeHeatQ3RefinedCarrierChild, parent, e,
      Equiv.symm_apply_apply]
  have hactive : ∀ y ij, ij ∈ U y ↔
      y ∈ q3ExpandedRectangle (a₀ ij) (a₁ ij) (b₀ ij) (b₁ ij) (Lfun ij) := by
    intro y ij
    change ij ∈ nativeHeatQ3RefinedGridActiveFinset parent L y ↔ _
    simp only [nativeHeatQ3RefinedGridActiveFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hy
      have hphysical : y ∈ q3ExpandedRectangle
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 0)
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedChildCube parent ij))
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 1)
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedChildCube parent ij)) L := by
        change y ∈ q3ExpandedRectangle
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 0)
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedChildCube parent ij))
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 1)
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedChildCube parent ij)) L
        exact hy
      simpa only [a₀, a₁, b₀, b₁, Lfun, hchild ij] using hphysical
    · intro hy
      have hphysical : y ∈ q3ExpandedRectangle
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 0)
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedChildCube parent ij))
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 1)
          (cubeCorner (nativeHeatQ3RefinedChildCube parent ij) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedChildCube parent ij)) L := by
        simpa only [a₀, a₁, b₀, b₁, Lfun, hchild ij] using hy
      exact hphysical
  have hrect (ij : I) : a₀ ij < a₁ ij ∧ b₀ ij < b₁ ij := by
    have hside : 0 < cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m (e ij)) := by
      dsimp [cubeScaleFactor]
      positivity
    constructor <;> dsimp [a₀, a₁, b₀, b₁] <;> linarith
  have hN : 0 < N := by
    dsimp [N, I]
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr
      (show Nonempty (Fin (3 ^ 10) × Fin (3 ^ 10)) from
        ⟨⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩))
  have hratio (y : Vec 2) : (U y).card / N ≤ q3GridOverlapFactor 10 s := by
    have hraw := nativeHeatQ3RefinedGridSupportOverlap_card_ratio_le
      parent s hsLower hsUpper L hL y
    have hmap : (U y).card = (active y).card := rfl
    rw [hmap]
    change ((active y).card : ℝ) / (Fintype.card I : ℝ) ≤ _
    simpa only [Finset.card_univ] using hraw
  have hoverlap : ∀ y : Vec 2, ((S ∩ U y).card : ℝ) ≤ C₀ := by
    intro y
    have hmul := (div_le_iff₀ hN).mp (hratio y)
    have hinter : S ∩ U y = U y := by simp [S]
    rw [hinter]
    change ((U y).card : ℝ) ≤ q3GridOverlapFactor 10 s * N
    exact hmul
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀, q3GridOverlapFactor]
    positivity
  have hab : ∀ ij ∈ S, a₀ ij < a₁ ij := by
    intro ij _
    exact (hrect ij).1
  have hcd : ∀ ij ∈ S, b₀ ij < b₁ ij := by
    intro ij _
    exact (hrect ij).2
  have hgeneric := q3RemainderRiesz_average_sq_le_support_overlap
    S a₀ a₁ b₀ b₁ β Lfun center O hab hcd C₀ hC₀ hN U hactive
      hoverlap
  have hgeneric' :
      ‖N⁻¹ • ∑ ij : I,
        (InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O ij).comp (factor ij))‖ ^ 2 ≤
        C₀ * N⁻¹ ^ 2 * ∑ ij : I,
          ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
            ((O ij).comp (factor ij))‖ ^ 2 := by
    simpa only [N, S, Finset.card_univ] using hgeneric
  have hNne : N ≠ 0 := ne_of_gt hN
  have hcoef : C₀ * N⁻¹ ^ 2 = q3GridOverlapFactor 10 s * N⁻¹ := by
    dsimp [C₀]
    field_simp [hNne]
  have hoverlapAvg :
      ‖N⁻¹ • ∑ ij : I,
        (InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O ij).comp (factor ij))‖ ^ 2 ≤
        q3GridOverlapFactor 10 s * N⁻¹ *
          ∑ ij : I,
            ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
              ((O ij).comp (factor ij))‖ ^ 2 := by
    calc
      _ ≤ C₀ * N⁻¹ ^ 2 * ∑ ij : I,
          ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
            ((O ij).comp (factor ij))‖ ^ 2 := hgeneric'
      _ = _ := by rw [hcoef]
  let c₀ : ℝ := 4 * (amp ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2
  have hrow (ij : I) :
      ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O ij).comp (factor ij))‖ ^ 2 ≤ c₀ * profile (e ij) := by
    let ci := e ij
    let Q := nativeHeatQ3RefinedCarrierChild m ci
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let B := lemmaVTileHistory (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ
        (pureFluxOpenResponseRestriction Q.scale (A (x ci))))
    let T := modelTraceObservable Q.scale M.nu σ (A (x ci))
    let ampChild := q3ModelAmplitude M h
      (Q.scale + ((d.val : ℤ) + 2))
    let lengthChild := q3ModelLength (Q.scale + ((d.val : ℤ) + 2))
    let ρChild := cubeScaleFactor (originCube 2 Q.scale) / lengthChild.1
    let δChild := diagMeshRadius (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s) / lengthChild.1
    let childFactor := q3RemainderValueFactor
      (a₀ ij) (a₁ ij) (b₀ ij) (b₁ ij)
      ampChild lengthChild (center ij)
    have hscaleChild : Q.scale = m := by
      exact nativeHeatQ3RefinedCarrierChild_scale m ci
    have hsCast : ((d.val + 2 : ℕ) : ℤ) = (d.val : ℤ) + 2 := by
      norm_num
    have harg : m + (s : ℤ) = Q.scale + ((d.val : ℤ) + 2) := by
      rw [hscaleChild]
      simp [s]
    have hampChild : ampChild = amp := by
      change q3ModelAmplitude M h (Q.scale + ((d.val : ℤ) + 2)) = _
      exact congrArg (q3ModelAmplitude M h) harg.symm
    have hlengthChild : lengthChild = L := by
      change q3ModelLength (Q.scale + ((d.val : ℤ) + 2)) = _
      exact congrArg q3ModelLength harg.symm
    have hρChild : ρChild = ρ := by
      change cubeScaleFactor (originCube 2 Q.scale) /
          (q3ModelLength (Q.scale + ((d.val : ℤ) + 2))).1 =
        cubeScaleFactor (originCube 2 m) / L.1
      rw [← hlengthChild]
      simp only [lengthChild, Q, ci, hscaleChild]
    have hδChild : δChild = δ := by
      change diagMeshRadius (originCube 2 Q.scale)
          (pureFluxBankSourceDepth s) /
            (q3ModelLength (Q.scale + ((d.val : ℤ) + 2))).1 =
        diagMeshRadius (originCube 2 m) (pureFluxBankSourceDepth s) / L.1
      rw [← hlengthChild]
      simp only [lengthChild, Q, ci, hscaleChild]
    have hFactor : factor ij = childFactor := by
      simp only [factor, childFactor, a₀, a₁, b₀, b₁, β, Lfun, center]
      rw [← hampChild, ← hlengthChild]
    have hi := nativeHeatQ3RefinedCarrierChildMeanObservationRiesz_sq_le
      M h hM m ci d σ hσ x
    have hi' :
        ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
            ((O ij).comp childFactor)‖ ^ 2 ≤
          4 * (ampChild ^ 2 / σ ^ 2) * (lemmaVH2Bn ρChild δChild) ^ 2 *
            B ^ 2 * T * (T + 4) := hi
    calc
      _ = ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O ij).comp childFactor)‖ ^ 2 := by rw [hFactor]
      _ ≤ 4 * (ampChild ^ 2 / σ ^ 2) * (lemmaVH2Bn ρChild δChild) ^ 2 *
          B ^ 2 * T * (T + 4) := hi'
      _ = c₀ * profile (e ij) := by
        rw [hampChild, hρChild, hδChild]
        simp only [c₀, profile, Q, A, B, T]
        ring
  have hprofile :
      (∑ ij : I,
        ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O ij).comp (factor ij))‖ ^ 2) ≤
        c₀ * ∑ ij : I, profile (e ij) := by
    calc
      _ ≤ ∑ ij : I, c₀ * profile (e ij) :=
        Finset.sum_le_sum fun ij _ => hrow ij
      _ = c₀ * ∑ ij : I, profile (e ij) := by rw [← Finset.mul_sum]
  have hcoefNonneg : 0 ≤ q3GridOverlapFactor 10 s * N⁻¹ := by
    dsimp [q3GridOverlapFactor]
    positivity
  let Rcarrier : C → WhiteNoise := fun i =>
    (InnerProductSpace.toDual ℝ WhiteNoise).symm
      ((nativeHeatQ3RefinedChildMeanTraceObservation M σ m x i).comp
        (q3RemainderValueFactor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          amp L
          ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
            nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
              (subset_closure
                (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                  (nativeHeatQ3RefinedCarrierChild m i)))⟩))
  let Rprod : I → WhiteNoise := fun ij =>
    (InnerProductSpace.toDual ℝ WhiteNoise).symm ((O ij).comp (factor ij))
  have hRprod (ij : I) : Rprod ij = Rcarrier (e ij) := rfl
  have hsumR : (∑ i : C, Rcarrier i) = ∑ ij : I, Rprod ij := by
    calc
      _ = ∑ ij : I, Rcarrier (e ij) :=
        (Equiv.sum_comp e Rcarrier).symm
      _ = ∑ ij : I, Rprod ij := by
        apply Finset.sum_congr rfl
        intro ij _
        exact (hRprod ij).symm
  have hsumNorm :
      (∑ i : C, ‖Rcarrier i‖ ^ 2) =
        ∑ ij : I, ‖Rprod ij‖ ^ 2 := by
    calc
      _ = ∑ ij : I, ‖Rcarrier (e ij)‖ ^ 2 :=
        (Equiv.sum_comp e (fun i => ‖Rcarrier i‖ ^ 2)).symm
      _ = ∑ ij : I, ‖Rprod ij‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro ij _
        rw [← hRprod ij]
  have hsumProfile : (∑ i : C, profile i) = ∑ ij : I, profile (e ij) :=
    (Equiv.sum_comp e profile).symm
  have hcard : (Fintype.card C : ℝ) = N := by
    dsimp [N, I, C]
    exact_mod_cast (Fintype.card_congr e).symm
  have hmean :
      ((Fintype.card C : ℝ)⁻¹) • ∑ i : C, Rcarrier i =
        N⁻¹ • ∑ ij : I, Rprod ij := by
    rw [hsumR, hcard]
  calc
    _ = ‖N⁻¹ • ∑ ij : I, Rprod ij‖ ^ 2 := by rw [hmean]
    _ ≤ q3GridOverlapFactor 10 s * N⁻¹ * ∑ ij : I, ‖Rprod ij‖ ^ 2 := by
      exact hoverlapAvg
    _ ≤ q3GridOverlapFactor 10 s * N⁻¹ *
          (c₀ * ∑ ij : I, profile (e ij)) :=
      mul_le_mul_of_nonneg_left hprofile hcoefNonneg
    _ = 4 * (amp ^ 2 / σ ^ 2) * q3GridOverlapFactor 10 s *
          (lemmaVH2Bn ρ δ) ^ 2 *
            ((Fintype.card C : ℝ)⁻¹ * ∑ i : C, profile i) := by
      rw [hsumProfile, ← hcard]
      simp only [c₀]
      ring

end ASDExplicitGamma.Native
