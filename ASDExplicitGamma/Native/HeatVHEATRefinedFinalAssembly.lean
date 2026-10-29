module

public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly
public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssembly
public import ASDExplicitGamma.Native.HeatVHEATRefinedAuxiliary
public import ASDExplicitGamma.Native.HeatVHEATCarrierRow
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservation
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNorms
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActual
public import ASDExplicitGamma.Native.HeatRefinedFamilyProfiles

/-! Exact final joins for the refined VHEAT generator. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
open scoped ENNReal NNReal
noncomputable section

local instance heatVHEATRefinedFinalChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

local instance heatVHEATRefinedFinalChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- The actual mean covariance with its exact center covariance removed is
bounded by the normalized off-diagonal child profiles. The diagonal profile
cancels before any estimate is applied. -/
theorem nativeHeatQ3RefinedCarrierMeanCovariance_minus_center_le_offDiagonal
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let I := childConstantMap V
    let C₀ := childCenterMap (nativeHeatQ3RefinedCarrierCenter m)
    let H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) :=
      fun j => nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j)
    let P := nativeHeatQ3RefinedCarrierOldMap m
    (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P (H j)) x -
      (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => I (C₀ (H j))) x ≤
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ (x i)) := by
  classical
  intro Q U hU hvol V μ I C₀ H P
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    change Summable (fun j =>
      ‖nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j)‖ ^ 2)
    exact summable_sq_norm_map
      (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) =
      ((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ) := by
    norm_num [nativeHeatQ3RefinedCarrierIndex]
  have hmean := nativeHeat_childMeanTrace_covarianceTrace
    Q M.nu σ M.nu_pos hσ hH P x
  have hcenter := nativeHeatQ3RefinedCarrierMeanCenterCovariance_eq_profileRows
    M h hM m σ hσ x
  let childCov : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    modelCovarianceTrace
      (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
      (fun j => (P (H j)) i) (x i)
  let childCenter : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    ∑ d : Fin 9,
      nativeHeatQ3RefinedCarrierChildCenterDriftProfile M h m i d σ (x i)
  let childOff : nativeHeatQ3RefinedCarrierIndex → ℝ := fun i =>
    ∑ d : Fin 9,
      nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d σ (x i)
  have hchild (i : nativeHeatQ3RefinedCarrierIndex) :
      (1 / 2 : ℝ) * childCov i - childCenter i ≤ childOff i := by
    change (1 / 2 : ℝ) * modelCovarianceTrace
        (childTraceObservable (hU i) (hvol i) M.nu σ M.nu_pos hσ)
        (fun j => (nativeHeatQ3RefinedCarrierOldMap m
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
            (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j))) i)
        (x i) -
        ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildCenterDriftProfile M h m i d σ (x i) ≤
      ∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d σ (x i)
    exact nativeHeatQ3RefinedCarrierChildCenteredCovariance_le_offDiagonalProfiles
      M h hM m i σ hσ (x i)
  have hchildsum : (∑ i : nativeHeatQ3RefinedCarrierIndex,
      ((1 / 2 : ℝ) * childCov i - childCenter i)) ≤
      ∑ i : nativeHeatQ3RefinedCarrierIndex, childOff i :=
    Finset.sum_le_sum (fun i _ => hchild i)
  have hcardNonneg : 0 ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hmean' : modelCovarianceTrace μ (fun j => P (H j)) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childCov i := by
    rw [hcard]
    exact hmean
  have hcenter' : (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => I (C₀ (H j))) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i := by
    change (1 / 2 : ℝ) * modelCovarianceTrace μ
        (fun j => I (C₀ (H j))) x =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i
    exact hcenter
  calc
    _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          ((1 / 2 : ℝ) * childCov i - childCenter i) := by
          rw [hmean', hcenter']
          calc
            _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
                ((1 / 2 : ℝ) *
                    ∑ i : nativeHeatQ3RefinedCarrierIndex, childCov i -
                  ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i) := by ring
            _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
                ((∑ i : nativeHeatQ3RefinedCarrierIndex,
                    (1 / 2 : ℝ) * childCov i) -
                  ∑ i : nativeHeatQ3RefinedCarrierIndex, childCenter i) := by
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.sum_sub_distrib]
    _ ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, childOff i :=
      mul_le_mul_of_nonneg_left hchildsum hcardNonneg
    _ = (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ (x i) := by rfl

private theorem nativeHeatVHEATJ_mono_X_p20_of_nonneg
    (ε F X₁ X₂ : ℝ) (j l : ℕ)
    (hε : 0 ≤ ε) (hF : 0 ≤ F) (hX₁ : 0 ≤ X₁) (hX₂ : 0 < X₂)
    (hX : X₁ ≤ X₂) (hj : j ≤ 2) (hl : l ≤ 20) :
    nativeHeatVHEATJ ε X₁ F 20 j l ≤ nativeHeatVHEATJ ε X₂ F 20 j l := by
  by_cases hX₁pos : 0 < X₁
  · exact nativeHeatVHEATJ_mono_X_p20 ε F X₁ X₂ j l
      hε hF hX₁pos hX hj hl
  · have hX₁zero : X₁ = 0 := le_antisymm (le_of_not_gt hX₁pos) hX₁
    subst X₁
    by_cases hlt : l < 20
    · by_cases hlzero : l = 0
      · subst l
        simp [nativeHeatVHEATJ, hlt]
      · have hlpos : 0 < l := Nat.pos_of_ne_zero hlzero
        simp [nativeHeatVHEATJ, hlt, Nat.ne_of_gt hlpos]
        exact mul_nonneg (pow_nonneg hε j) (pow_nonneg hX₂.le l)
    · have hle : l = 20 := by omega
      subst l
      have hleft : nativeHeatVHEATJ ε 0 F 20 j 20 = 0 := by
        simp [nativeHeatVHEATJ]
      rw [hleft]
      have hright : 0 ≤ nativeHeatVHEATJ ε X₂ F 20 j 20 := by
        rw [nativeHeatVHEATJ_top]
        exact mul_nonneg
          (mul_nonneg (pow_nonneg hε j) (pow_nonneg hX₂.le 20))
          (Real.rpow_nonneg (div_nonneg hF hX₂.le) _)
      exact hright

/-- The degree-20 VHEAT error is monotone in its trace cap even when the
lower cap is zero. This boundary case is needed when converting the
time-local extended-norm output to the uniform contract tuple. -/
theorem nativeHeatVHEATErrorEk_mono_X_p20_of_nonneg
    (k : ℕ) (e_h K M S_B θ b X₁ X₂ Y ε F : ℝ)
    (hk : k ≤ 20)
    (he : 0 ≤ e_h) (hK : 0 ≤ K) (hM : 0 ≤ M) (hSB : 0 ≤ S_B)
    (hθ : 0 < θ) (hb : 0 ≤ b) (hX₁ : 0 ≤ X₁)
    (hX₂ : 0 < X₂) (hX : X₁ ≤ X₂)
    (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hF : 0 ≤ F) :
    nativeHeatVHEATErrorEk k 20 e_h K M S_B θ b X₁ Y ε F ≤
      nativeHeatVHEATErrorEk k 20 e_h K M S_B θ b X₂ Y ε F := by
  by_cases hX₁pos : 0 < X₁
  · exact nativeHeatVHEATErrorEk_mono_X_p20 k e_h K M S_B θ b X₁ X₂ Y ε F
      hk he hK hM hSB hθ hb hX₁pos hX hY hε hF
  · have hX₁zero : X₁ = 0 := le_antisymm (le_of_not_gt hX₁pos) hX₁
    subst X₁
    let JL : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε 0 F 20
    let JR : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X₂ F 20
    have hJ (j l : ℕ) (hj : j ≤ 2) (hl : l ≤ 20) : JL j l ≤ JR j l := by
      exact nativeHeatVHEATJ_mono_X_p20_of_nonneg ε F 0 X₂ j l
        hε hF (by norm_num) hX₂ (by linarith) hj hl
    have hkminus : k - 1 ≤ 20 := by omega
    have hsum1 : 4 * JL 1 (k - 1) + JL 1 k ≤
        4 * JR 1 (k - 1) + JR 1 k := by
      have h1 := hJ 1 (k - 1) (by norm_num) hkminus
      have h2 := hJ 1 k (by norm_num) hk
      nlinarith [h1, h2]
    have hsum2 : 4 * JL 2 (k - 1) + JL 2 k ≤
        4 * JR 2 (k - 1) + JR 2 k := by
      have h1 := hJ 2 (k - 1) (by norm_num) hkminus
      have h2 := hJ 2 k (by norm_num) hk
      nlinarith [h1, h2]
    have hcoef1 : 0 ≤ 2 * K + 2 * b * M := by positivity
    have hfirst :
        (2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
          M * (4 * JL 2 (k - 1) + JL 2 k) ≤
        (2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
          M * (4 * JR 2 (k - 1) + JR 2 k) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hcoef1)
        (mul_le_mul_of_nonneg_left hsum2 hM)
    have hbase :
        (k : ℝ) * e_h *
            ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
              M * (4 * JL 2 (k - 1) + JL 2 k)) ≤
        (k : ℝ) * e_h *
            ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
              M * (4 * JR 2 (k - 1) + JR 2 k)) := by
      exact mul_le_mul_of_nonneg_left hfirst
        (mul_nonneg (Nat.cast_nonneg k) he)
    have hquad : 4 * (0 : ℝ) + (0 : ℝ) ^ 2 ≤ 4 * X₂ + X₂ ^ 2 := by
      norm_num
      exact add_nonneg (mul_nonneg (by norm_num) hX₂.le) (sq_nonneg X₂)
    have hbracket :
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * (0 : ℝ) + (0 : ℝ) ^ 2) +
              2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
              4 * JL 2 (k - 1) + JL 2 k)
         else 0) ≤
        (if 2 ≤ k then
          2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
            (b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) +
              2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
              4 * JR 2 (k - 1) + JR 2 k)
         else 0) := by
      by_cases hk₂ : 2 ≤ k
      · simp [hk₂]
        have hcoeff : 0 ≤
            2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) := by
          have hkR1 : (1 : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (show 1 ≤ k by omega)
          have hkSub : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr hkR1
          have hθfactor : 0 ≤ 1 + θ⁻¹ :=
            add_nonneg (by norm_num) (inv_nonneg.mpr hθ.le)
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hkSub) he) hSB)
            hθfactor
        have hXterm :
            b ^ 2 * Y ^ (k - 2) * (4 * (0 : ℝ) + (0 : ℝ) ^ 2) ≤
              b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hquad
            (mul_nonneg (sq_nonneg b) (pow_nonneg hY _))
        have hJterm :
            2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
                4 * JL 2 (k - 1) + JL 2 k ≤
              2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
                4 * JR 2 (k - 1) + JR 2 k := by
          have hB := mul_le_mul_of_nonneg_left hsum1
            (by positivity : 0 ≤ 2 * b)
          nlinarith only [hB, hsum2]
        have hinner :
            b ^ 2 * Y ^ (k - 2) * (4 * (0 : ℝ) + (0 : ℝ) ^ 2) +
                2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
                4 * JL 2 (k - 1) + JL 2 k ≤
              b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) +
                2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
                4 * JR 2 (k - 1) + JR 2 k := by
          nlinarith only [hXterm, hJterm]
        exact mul_le_mul_of_nonneg_left (by simpa using hinner) hcoeff
      · simp [hk₂]
    change
        (k : ℝ) * e_h *
            ((2 * K + 2 * b * M) * (4 * JL 1 (k - 1) + JL 1 k) +
              M * (4 * JL 2 (k - 1) + JL 2 k)) +
          (if 2 ≤ k then
            2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
              (b ^ 2 * Y ^ (k - 2) * (4 * (0 : ℝ) + (0 : ℝ) ^ 2) +
                2 * b * (4 * JL 1 (k - 1) + JL 1 k) +
                4 * JL 2 (k - 1) + JL 2 k)
           else 0) ≤
        (k : ℝ) * e_h *
            ((2 * K + 2 * b * M) * (4 * JR 1 (k - 1) + JR 1 k) +
              M * (4 * JR 2 (k - 1) + JR 2 k)) +
          (if 2 ≤ k then
            2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
              (b ^ 2 * Y ^ (k - 2) * (4 * X₂ + X₂ ^ 2) +
                2 * b * (4 * JR 1 (k - 1) + JR 1 k) +
                4 * JR 2 (k - 1) + JR 2 k)
           else 0)
    exact add_le_add hbase hbracket

end
end ASDExplicitGamma.Native
