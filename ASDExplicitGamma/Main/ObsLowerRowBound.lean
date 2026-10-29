module

public import ASDExplicitGamma.Main.ObsLowerDistinctRow
public import ASDExplicitGamma.Main.ObsLowerRowPairing
public import ASDExplicitGamma.Main.ObsLowerCoercivityVar
public import ASDExplicitGamma.Main.InverseLowerRowBound

/-! Observer-level (depth `m` source mesh) uncentered q3 row pairings against actual response variations. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Main

local instance obsRowBoundFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

/-- The distinct q3 row, with a different H10 potential in every
covariance direction, pairs against a common H1 gradient with the normalized
source coefficient. -/
theorem obs_distinct_h10_row_pairing_bound
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l})
    (s : Finset whiteBasisIndex) (m : ℕ)
    (z : whiteBasisIndex → H10Function (openCubeSet (originCube 2 n)))
    (g : H1Function (openCubeSet (originCube 2 n))) :
    let Q := originCube 2 n
    let U := openCubeSet Q
    let Sphys : Vec 2 → Vec 2 := fun x => ∑ l ∈ s,
      lemmaVPlanarRowField (diagInterpolant Q m)
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l)
        (z l).toH1Function x
    |volumeAverage U (fun x => vecDot (Sphys x) (g.grad x))| ≤
      |σ⁻¹| * mainQ3RowConstant (diagMeshRadius (originCube 2 n) m) b L.1 *
        Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m
          (z l).toH1Function.grad) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let I := diagInterpolant Q m
  let Sraw := obsDistinctRow whiteBasis s b L Q m z
  let Sphys : Vec 2 → Vec 2 := fun x => ∑ l ∈ s,
    lemmaVPlanarRowField I (pureFluxMainQ3BasisFrameMultiplier n b σ L l)
      (z l).toH1Function x
  have hSscale : Sphys = fun x => (σ⁻¹ : ℝ) • Sraw x := by
    funext x
    dsimp [Sphys, Sraw, obsDistinctRow,
      pureFluxMainQ3BasisFrameMultiplier]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact congrFun (pureFluxPlanarRowField_smul I
      (mainQ3DirectionW2 Q b L (whiteBasis l)).value
      (z l).toH1Function (σ⁻¹)) x
  have hηraw (l : whiteBasisIndex) :
      MemLp ((mainQ3DirectionW2 Q b L (whiteBasis l)).value.toFun)
        (⊤ : ENNReal) (volume.restrict U) :=
    (mainQ3DirectionW2 Q b L (whiteBasis l)).value_memLp_top
  have hDηraw (l : whiteBasisIndex) (j : Fin 2) :
      MemLp (fun x => (mainQ3DirectionW2 Q b L
        (whiteBasis l)).value.grad x j) (⊤ : ENNReal) (volume.restrict U) :=
    (mainQ3DirectionW2 Q b L (whiteBasis l)).gradient_memLp_top_volume j
  have hSrawMem : MemVectorL2 U Sraw := by
    change MemLp (fun x => ∑ l ∈ s, lemmaVPlanarRowField I
      (mainQ3DirectionW2 Q b L (whiteBasis l)).value
      (z l).toH1Function x) 2 (volumeMeasureOn U)
    exact memLp_finsetSum s fun l hl => lemmaVPlanarRowField_memL2 I
      (mainQ3DirectionW2 Q b L (whiteBasis l)).value
      (z l).toH1Function (hηraw l) (hDηraw l)
  have hSrawCoord (j : Fin 2) : MemLp (fun x => Sraw x j) 2
      (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (hSrawMem.eval j)
  have hrow := obs_distinct_h10_row_bound
    whiteBasis s b L Q m z
  have hdual : |volumeAverage U (fun x => vecDot (Sraw x) (g.grad x))| ≤
      Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q m Sraw) := by
    change |integralAverage U (fun x => vecDot (Sraw x) (g.grad x))| ≤ _
    rw [← cubeAverage_eq_integralAverage_openCubeSet]
    have hcomm : (fun x => vecDot (Sraw x) (g.grad x)) =
        fun x => vecDot (g.grad x) (Sraw x) := by
      funext x
      exact vecDot_comm _ _
    rw [hcomm]
    exact lemmaV_tiled_pairing_le Q m g.grad_memL2_normalizedCubeMeasure
      hSrawCoord hrow.1
  have hrawBound :
      |volumeAverage U (fun x => vecDot (Sraw x) (g.grad x))| ≤
        Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
          (mainQ3RowConstant (diagMeshRadius Q m) b L.1 * Real.sqrt
            (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad)) := by
    exact hdual.trans (mul_le_mul_of_nonneg_left hrow.2 (Real.sqrt_nonneg _))
  have hscaleAvg : volumeAverage U (fun x => vecDot (Sphys x) (g.grad x)) =
      (σ⁻¹ : ℝ) * volumeAverage U (fun x => vecDot (Sraw x) (g.grad x)) := by
    calc
      _ = volumeAverage U (fun x => (σ⁻¹ : ℝ) *
          vecDot (Sraw x) (g.grad x)) := by
        congr 1
        funext x
        rw [hSscale]
        simp only [vecDot, Pi.smul_apply, Fin.sum_univ_two]
        ring
      _ = volumeAverage U ((σ⁻¹ : ℝ) •
          (fun x => vecDot (Sraw x) (g.grad x))) := by rfl
      _ = _ := volumeAverage_smul U (σ⁻¹)
        (fun x => vecDot (Sraw x) (g.grad x))
  change |volumeAverage U (fun x => vecDot (Sphys x) (g.grad x))| ≤ _
  rw [hscaleAvg, abs_mul]
  calc
    _ ≤ |σ⁻¹| * (Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) *
        (mainQ3RowConstant (diagMeshRadius Q m) b L.1 * Real.sqrt
          (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad))) :=
      mul_le_mul_of_nonneg_left hrawBound (abs_nonneg _)
    _ = _ := by ring

/-- A finite family of actual response variations admits q3 row
pairings at every source depth, with each chosen H10 representative controlled
by its response-energy norm. -/
theorem obs_variation_family_shear_pairing_bound
    (n : ℤ) (m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (B : ℝ)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B)
    (Y : whiteBasisIndex →
      (responseFrameEnergyVariationSpace
        (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
        ν σ hν hσ k).toSubmodule) :
    ∃ z : whiteBasisIndex → H10Function (openCubeSet (originCube 2 n)),
      (∀ l, (fun x => (hilbertBlockL2ToBlockL2
          ((Y l : EnergyCarrier (responseFrameEnergyData
            (measurableSet_openCubeSet (originCube 2 n))
            (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
            ν σ hν hσ k))).down x).1) =ᵐ[
            volumeMeasureOn (openCubeSet (originCube 2 n))]
          (z l).toH1Function.grad) ∧
      (∀ l, lemmaVTiledWeakEnergy (originCube 2 n) m
          (z l).toH1Function.grad ≤
        B * ‖(Y l : EnergyCarrier (responseFrameEnergyData
          (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k))‖^2) ∧
      |∑ l ∈ s, inner ℝ
          (responseFrameEnergyBaseMinimizer
            (measurableSet_openCubeSet (originCube 2 n))
            (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
            ν σ hν hσ k P)
          (responseFrameEnergyShearFamily
            (measurableSet_openCubeSet (originCube 2 n))
            (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
            ν σ hν hσ k
            (pureFluxMainCubeQ3ResponseCoefficient n b L
              (@Encodable.encode whiteBasisIndex
                (Encodable.ofCountable whiteBasisIndex) l))
            (Y l : EnergyCarrier (responseFrameEnergyData
              (measurableSet_openCubeSet (originCube 2 n))
              (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
              ν σ hν hσ k)))| ≤
        |σ⁻¹| * mainQ3RowConstant (diagMeshRadius (originCube 2 n) m) b L.1 *
          Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy (originCube 2 n) m
            (z l).toH1Function.grad) *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 n) m
            ((1 / 2 : ℝ) • (w.toH1-u.toH1)).grad) := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q)
    (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
    (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily (measurableSet_openCubeSet Q)
    (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
  let g : H1Function U := (1 / 2 : ℝ) • (w.toH1-u.toH1)
  let H (l : whiteBasisIndex) := pureFluxMainCubeQ3ResponseCoefficient n b L
    (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)
  let η (l : whiteBasisIndex) := pureFluxMainQ3BasisFrameMultiplier n b σ L l
  let z (l : whiteBasisIndex) := Classical.choose
    (obs_variation_first_potential_weak_energy_bound
      n m ν σ hν hσ k (Y l) B hhist)
  have hz (l : whiteBasisIndex) := (Classical.choose_spec
    (obs_variation_first_potential_weak_energy_bound
      n m ν σ hν hσ k (Y l) B hhist)).1
  have hzTiled (l : whiteBasisIndex) := (Classical.choose_spec
    (obs_variation_first_potential_weak_energy_bound
      n m ν σ hν hσ k (Y l) B hhist)).2
  have hrowDir (l : whiteBasisIndex) (hl : l ∈ s) :
      inner ℝ S (C (H l) (Y l : EnergyCarrier D)) =
        volumeAverage U (fun x => vecDot
          (lemmaVPlanarRowField (diagInterpolant Q m) (η l)
            (z l).toH1Function x) (g.grad x)) := by
    have hp := obs_response_shear_pairing_eq_diag_row_of_first_potential
      n ν σ b hν hσ L l m k P u w hrep (Y l : EnergyCarrier D) (z l) (hz l)
    simpa [Q, U, D, S, C, H, η, g] using hp
  have hsumPair : (∑ l ∈ s, inner ℝ S (C (H l) (Y l : EnergyCarrier D))) =
      volumeAverage U (fun x => vecDot
        (∑ l ∈ s, lemmaVPlanarRowField (diagInterpolant Q m) (η l)
          (z l).toH1Function x) (g.grad x)) := by
    calc
      _ = ∑ l ∈ s, volumeAverage U (fun x => vecDot
          (lemmaVPlanarRowField (diagInterpolant Q m) (η l)
            (z l).toH1Function x) (g.grad x)) := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hrowDir l hl
      _ = volumeAverage U (fun x => ∑ l ∈ s, vecDot
          (lemmaVPlanarRowField (diagInterpolant Q m) (η l)
            (z l).toH1Function x) (g.grad x)) := by
        rw [volumeAverage_sum]
        intro l hl
        have hηraw : MemLp ((mainQ3DirectionW2 Q b L
            (whiteBasis l)).value.toFun) (⊤ : ENNReal) (volume.restrict U) :=
          (mainQ3DirectionW2 Q b L (whiteBasis l)).value_memLp_top
        have hDηraw (j : Fin 2) : MemLp (fun x =>
            (mainQ3DirectionW2 Q b L (whiteBasis l)).value.grad x j)
              (⊤ : ENNReal) (volume.restrict U) :=
          (mainQ3DirectionW2 Q b L
            (whiteBasis l)).gradient_memLp_top_volume j
        have hη : MemLp (η l).toFun (⊤ : ENNReal) (volume.restrict U) := by
          dsimp [η, pureFluxMainQ3BasisFrameMultiplier]
          simpa only [H1Function.smul_toFun, smul_eq_mul, mul_comm] using
            hηraw.const_mul (σ⁻¹)
        have hDη (j : Fin 2) : MemLp (fun x => (η l).grad x j)
            (⊤ : ENNReal) (volume.restrict U) := by
          dsimp [η, pureFluxMainQ3BasisFrameMultiplier]
          simpa only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul] using
            (hDηraw j).const_mul (σ⁻¹)
        exact integrableOn_vecDot_of_memVectorL2
          (lemmaVPlanarRowField_memL2 (diagInterpolant Q m) (η l)
            (z l).toH1Function hη hDη) g.grad_memVectorL2
      _ = _ := by
        congr 1
        funext x
        simp only [vecDot]
        rw [Finset.sum_comm]
        simp only [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_mul]
  refine ⟨z, ?_, ?_, ?_⟩
  · intro l
    simpa [Q, D] using hz l
  · intro l
    simpa [Q, z] using hzTiled l
  · rw [hsumPair]
    simpa [Q, U, D, η, g] using
      obs_distinct_h10_row_pairing_bound n b σ L s m z g

end ASDExplicitGamma.Main

end
