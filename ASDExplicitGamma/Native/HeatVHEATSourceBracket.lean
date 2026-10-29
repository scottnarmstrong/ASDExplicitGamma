module

public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrier
public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssembly
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrier

/-! The source-carrier rank-one bracket, with its excess center term absorbed
by Young's inequality before applying the shell profile rows. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal Topology

noncomputable section

local instance nativeHeatVHEATSourceBracketIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatVHEATSourceBracketChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The source-carrier second-order bracket has the exact negative excess
center square. Young absorbs it, and the remaining centered shell energy is
bounded by the actual source profiles with no center-clock payment. -/
theorem nativeHeatQ3RefinedCarrierSourceCenteredPowerBracket_le_profileRows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ : ℝ) (hθ : 0 < θ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (r : ℕ) (hr : 2 ≤ r) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let σ : ℝ := Annealed.sigmaBar M (m + 1)
    let hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let I := childConstantMap V
    let C₀ := nativeHeatQ3RefinedCarrierSourceCenterMap m
    let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
    let L := C₀
    let P := nativeHeatQ3RefinedCarrierOldMap m
    let R := P - I.comp L
    let D := fderiv ℝ μ x
    let coeff := (r : ℝ) * ((r : ℝ) - 1) * (μ x) ^ (r - 2)
    let B : (∀ i, C(V i, ℝ)) →L[ℝ] (∀ i, C(V i, ℝ)) →L[ℝ] ℝ :=
      coeff • D.smulRight D
    let H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
      fun j => nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j)
    let a : ℕ → ℝ := fun j => D (I (C₀ (H j)))
    let b : ℕ → ℝ := fun j => D (R₀ (H j))
    let sourceRows : ℝ :=
      ∑ d : Fin 9,
        4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 / σ ^ 2) *
          q3GridOverlapFactor 10 (d.val + 2) *
          (lemmaVH2Bn
            (cubeScaleFactor (originCube 2 m) /
              (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
            (diagMeshRadius (originCube 2 m)
              (pureFluxBankSourceDepth (d.val + 2)) /
              (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex,
              let Q := nativeHeatQ3RefinedCarrierChild m i
              let A := nativeHeat_translateTriadicFieldToOrigin Q
              let k := pureFluxOpenResponseRestriction Q.scale (A (x i))
              let B := lemmaVTileHistory (originCube 2 Q.scale)
                (pureFluxBankSourceDepth (d.val + 2))
                (responseFramePlanarCoefficientField M.nu σ k)
              let T := modelTraceObservable Q.scale M.nu σ (A (x i))
              B ^ 2 * T * (T + 4));
    (-θ * centerGenerator H L I B +
      mixedGenerator H L I R B +
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j))) =
        coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
          ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) ∧
    (-θ * centerGenerator H L I B +
      mixedGenerator H L I R B +
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) ≤
        (coeff / 2) * ((1 + θ⁻¹) * sourceRows)) := by
  classical
  intro Q U hU hvol V hV σ hσ μ I C₀ R₀ L P R D coeff B H a b sourceRows
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    change Summable (fun j =>
      ‖nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j)‖ ^ 2)
    exact summable_sq_norm_map
      (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)
  have hYoung := nativeHeatQ3RefinedCarrierSourceCenterRankOneResidualSplit
    M m θ hθ H hH x r hr
  have hRank :
      -θ * centerGenerator H L I B +
        mixedGenerator H L I R B +
        (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) =
      coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
        ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) := by
    exact hYoung.1
  have hYoungBound :
      -θ * centerGenerator H L I B +
        mixedGenerator H L I R B +
        (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) ≤
      (coeff / 2) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2) := by
    exact hYoung.2
  have hrow := nativeHeatQ3RefinedCarrierMeanRemainderBracket_sum
    M h hM m σ hσ x
  have hweighted := nativeHeatQ3RefinedCarrierPowerCenteredBracket_le_profileRows
    M h hM m σ hσ x r hr θ hθ hrow
  have hμnonneg : 0 ≤ μ x :=
    nativeHeat_childMeanTrace_nonneg (nativeHeatQ3RefinedCarrierChild m)
      M.nu σ M.nu_pos hσ x
  have hpow : Real.rpow (μ x) ((r : ℝ) - 2) = (μ x) ^ (r - 2) := by
    have hcast : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
      exact Nat.cast_sub hr
    rw [← hcast]
    exact Real.rpow_natCast _ _
  have hcoeffEq : (coeff / 2) * (1 + θ⁻¹) =
      ((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2) := by
    dsimp only [coeff]
    rw [hpow]
    ring
  have hgrad : modelGradientSquareTrace μ (fun j => R₀ (H j)) x =
      ∑' j, (b j) ^ 2 := by
    unfold modelGradientSquareTrace
    rfl
  have hweightedExact :
      (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2)) *
          modelGradientSquareTrace μ (fun j => R₀ (H j)) x ≤
      (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
        Real.rpow (μ x) ((r : ℝ) - 2)) * sourceRows := by
    simpa only [sourceRows] using hweighted
  have hweighted' :
      (coeff / 2) * (1 + θ⁻¹) * modelGradientSquareTrace μ
        (fun j => R₀ (H j)) x ≤ (coeff / 2) * (1 + θ⁻¹) * sourceRows := by
    calc
      _ = (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
          Real.rpow (μ x) ((r : ℝ) - 2)) *
            modelGradientSquareTrace μ (fun j => R₀ (H j)) x := by
              rw [hcoeffEq]
      _ ≤ (((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 + θ⁻¹) *
          Real.rpow (μ x) ((r : ℝ) - 2)) * sourceRows := hweightedExact
      _ = _ := by rw [← hcoeffEq]
  refine ⟨hRank, ?_⟩
  calc
    _ ≤ (coeff / 2) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2) := hYoungBound
    _ = (coeff / 2) * (1 + θ⁻¹) * modelGradientSquareTrace μ
        (fun j => R₀ (H j)) x := by rw [hgrad]; ring
    _ ≤ (coeff / 2) * (1 + θ⁻¹) * sourceRows := hweighted'
    _ = (coeff / 2) * ((1 + θ⁻¹) * sourceRows) := by ring

/-- For the actual unscaled source center map, the constant center drift is
nonnegative. Its excess contribution with coefficient `-θ` is nonpositive. -/
theorem nativeHeatQ3RefinedCarrierSourceCenterDrift_signOnSourceCarrier
    (M : ABKModel 2) (m : ℤ) (θ : ℝ) (hθ : 0 < θ)
    (H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ))
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (r : ℕ) (hr : 2 ≤ r) :
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i)
    let hU : ∀ i, MeasurableSet (U i) := fun i =>
      measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i =>
      volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let σ : ℝ := Annealed.sigmaBar M (m + 1)
    let hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let I := childConstantMap V
    let L := nativeHeatQ3RefinedCarrierSourceCenterMap m
    let centerDrift : ℝ :=
      (r : ℝ) * (μ x) ^ ((r : ℝ) - 1) *
        ((1 / 2 : ℝ) * modelCovarianceTrace μ
          (fun j => I (L (H j))) x);
    0 ≤ centerDrift ∧ -θ * centerDrift ≤ 0 := by
  classical
  intro U hU hvol V σ hσ μ I L centerDrift
  have hμnonneg : ∀ z, 0 ≤ μ z := by
    intro z
    exact nativeHeat_childMeanTrace_nonneg
      (nativeHeatQ3RefinedCarrierChild m) M.nu σ M.nu_pos hσ z
  have hcenter (j : ℕ) :
      0 ≤ secondDirectionalDerivative μ x (I (L (H j))) := by
    have hraw := nativeHeat_childMeanTrace_secondDirectional_nonneg
      (nativeHeatQ3RefinedCarrierChild m) M.nu σ M.nu_pos hσ x
      (fun _ => 0) (childCenterMap (nativeHeatQ3RefinedCarrierCenter m) (H j))
    have hIzero : I (fun _ : nativeHeatQ3RefinedCarrierIndex => (0 : ℝ)) = 0 :=
      map_zero I
    change 0 ≤ secondDirectionalDerivative μ
      (x + I (fun _ => 0)) (I (L (H j))) at hraw
    rw [hIzero, add_zero] at hraw
    simpa [L, nativeHeatQ3RefinedCarrierSourceCenterMap] using hraw
  have hcenterCov :
      0 ≤ (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => I (L (H j))) x := by
    rw [modelCovarianceTrace]
    exact mul_nonneg (by norm_num) (tsum_nonneg fun j => hcenter j)
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrNonneg : 0 ≤ (r : ℝ) := by linarith
  have hpower : 0 ≤ (μ x) ^ ((r : ℝ) - 1) :=
    Real.rpow_nonneg (hμnonneg x) _
  have hdrift : 0 ≤ centerDrift := by
    dsimp [centerDrift]
    exact mul_nonneg (mul_nonneg hrNonneg hpower) hcenterCov
  refine ⟨hdrift, ?_⟩
  calc
    -θ * centerDrift = -(θ * centerDrift) := by ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg hθ.le hdrift)

end
end ASDExplicitGamma.Native

end
