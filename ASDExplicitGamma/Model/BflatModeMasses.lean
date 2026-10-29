module

public import ASDExplicitGamma.Model.BflatCovariance
public import ASDExplicitGamma.Model.BflatModeParseval
public import ASDExplicitGamma.Model.BflatModeTransforms
public import ASDExplicitGamma.Model.BflatModal
public import ASDExplicitGamma.Model.Q3DerivativeMoments
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Integrated q3 feature energy and Fourier coefficient integrability -/

@[expose] public section

open MeasureTheory Set

namespace ASDExplicitGamma.Model

private theorem bflatIcc01_eq_interval (f : ℝ → ℝ) :
    (∫ x in Icc (0:ℝ) 1, f x) = ∫ x in (0:ℝ)..1, f x := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

/-- The total squared q3 feature energy on the unit interval is the point variance. -/
theorem bflatQ3FeatureEnergy_integral {ell : ℝ} (hell : 0 < ell) :
    (∫ y : ℝ, ∫ t in (0:ℝ)..1,
      (bflatQ3Feature ell y (t-1/2))^2) = 1 := by
  let a : ℝ := -(3/2)-ell
  let b : ℝ := (3/2)+ell
  let E : ℝ → ℝ := fun y => ∫ t in Icc (0:ℝ) 1,
    (bflatQ3Feature ell y (t-1/2))^2
  have hzero (y : ℝ) (hy : y ≤ a ∨ b ≤ y) : E y = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hx : t-1/2 ∈ Icc (-(1/2:ℝ)) (1/2) := by
      constructor <;> linarith [ht.1, ht.2]
    rcases hy with hy | hy
    · have hfar : y ≤ -(1/2:ℝ)-ell := by dsimp [a] at hy ⊢; linarith
      rw [bflatQ3Feature_zero_left hell hx hfar]
      simp [E]
    · have hfar : (1/2:ℝ)+ell ≤ y := by dsimp [b] at hy ⊢; linarith
      rw [bflatQ3Feature_zero_right hell hx hfar]
      simp [E]
  have hsupport : Function.support E ⊆ Ioc a b := by
    intro y hy
    have hne : E y ≠ 0 := by
      intro hz
      apply hy
      simp [hz]
    constructor
    · by_contra h
      exact hne (hzero y (Or.inl (le_of_not_gt h)))
    · by_contra h
      exact hne (hzero y (Or.inr (le_of_not_ge h)))
  have hfull : (∫ y : ℝ, E y) = ∫ y in a..b, E y := by
    exact (intervalIntegral.integral_eq_integral_of_support_subset hsupport).symm
  have hswapCont : Continuous (Function.uncurry (fun y t : ℝ =>
      (bflatQ3Feature ell y (t-1/2))^2)) := by
    change Continuous (fun p : ℝ×ℝ =>
      (bflatQ3Feature ell p.1 (p.2-1/2))^2)
    exact (bflatQ3Feature_centered_continuous ell).pow 2
  have hswapInt : IntegrableOn
      (Function.uncurry (fun y t : ℝ => (bflatQ3Feature ell y (t-1/2))^2))
      (uIoc a b ×ˢ uIoc (0:ℝ) 1) volume := by
    let R : Set (ℝ×ℝ) := uIcc a b ×ˢ uIcc (0:ℝ) 1
    have hcompact : IsCompact R := isCompact_uIcc.prod isCompact_uIcc
    have hclosed : IntegrableOn
        (Function.uncurry (fun y t : ℝ => (bflatQ3Feature ell y (t-1/2))^2))
        R volume := hswapCont.continuousOn.integrableOn_compact hcompact
    exact hclosed.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hinner {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
      (∫ y in a..b, (bflatQ3Feature ell y (t-1/2))^2) = 1 := by
    have hx : t-1/2 ∈ Icc (-(1/2:ℝ)) (1/2) := by
      constructor <;> linarith [ht.1, ht.2]
    have hsupp : Function.support (fun y : ℝ =>
        (bflatQ3Feature ell y (t-1/2))^2) ⊆ Ioc a b := by
      intro y hy
      have hne : bflatQ3Feature ell y (t-1/2) ≠ 0 := by
        change (bflatQ3Feature ell y (t-1/2))^2 ≠ 0 at hy
        intro hz
        apply hy
        rw [hz]
        simp
      constructor
      · by_contra h
        have hfar : y ≤ -(1/2:ℝ)-ell := by dsimp [a] at h ⊢; linarith
        exact hne (bflatQ3Feature_zero_left hell hx hfar)
      · by_contra h
        have hfar : (1/2:ℝ)+ell ≤ y := by dsimp [b] at h ⊢; linarith
        exact hne (bflatQ3Feature_zero_right hell hx hfar)
    calc
      _ = ∫ y : ℝ, (bflatQ3Feature ell y (t-1/2))^2 :=
        intervalIntegral.integral_eq_integral_of_support_subset hsupp
      _ = ASDExplicitGamma.q3Cov 0 := by
        have hcov := bflatQ3Feature_covariance hell (t-1/2) (t-1/2)
        simpa only [pow_two, sub_self, zero_div] using hcov
      _ = 1 := q3Cov_at_zero
  calc
    (∫ y : ℝ, ∫ t in (0:ℝ)..1,
        (bflatQ3Feature ell y (t-1/2))^2) = ∫ y : ℝ, E y := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact (bflatIcc01_eq_interval
        (fun t => (bflatQ3Feature ell y (t-1/2))^2)).symm
    _ = ∫ y in a..b, E y := hfull
    _ = ∫ y in a..b, ∫ t in (0:ℝ)..1,
        (bflatQ3Feature ell y (t-1/2))^2 := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact bflatIcc01_eq_interval
        (fun t => (bflatQ3Feature ell y (t-1/2))^2)
    _ = ∫ t in (0:ℝ)..1, ∫ y in a..b,
        (bflatQ3Feature ell y (t-1/2))^2 :=
      intervalIntegral_intervalIntegral_swap hswapInt
    _ =
      ∫ t in (0:ℝ)..1, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htcc : t ∈ Icc (0:ℝ) 1 := by
          simpa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
        exact hinner htcc
    _ = 1 := by simp

/-- The square of any continuous q3 feature coefficient is integrable in the
white-noise coordinate. -/
theorem bflatQ3FeatureCoeff_sq_integrable {ell : ℝ} (hell : 0 < ell)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun y : ℝ => (bflatQ3FeatureCoeff ell g y)^2) := by
  have hcoeffCont : Continuous (fun y : ℝ => bflatQ3FeatureCoeff ell g y) := by
    have hparam : Continuous (Function.uncurry (fun y : ℝ => fun t : ℝ =>
        bflatQ3Feature ell y (t-1/2) * g t)) := by
      change Continuous (fun p : ℝ×ℝ =>
        bflatQ3Feature ell p.1 (p.2-1/2) * g p.2)
      exact (bflatQ3Feature_centered_continuous ell).mul
        (hg.comp continuous_snd)
    change Continuous (fun y : ℝ =>
      ∫ t in Icc (0:ℝ) 1, bflatQ3Feature ell y (t-1/2) * g t)
    exact continuous_parametric_integral_of_continuous hparam isCompact_Icc
  let a : ℝ := -(3/2)-ell
  let b : ℝ := (3/2)+ell
  have hsupport : Function.support (fun y : ℝ =>
      (bflatQ3FeatureCoeff ell g y)^2) ⊆ Icc a b := by
    intro y hy
    have hne : bflatQ3FeatureCoeff ell g y ≠ 0 := by
      change (bflatQ3FeatureCoeff ell g y)^2 ≠ 0 at hy
      intro hz
      apply hy
      rw [hz]
      simp
    constructor
    · by_contra h
      have hfar : y ≤ -(3/2:ℝ)-ell := by dsimp [a] at h ⊢; linarith
      exact hne (bflatQ3FeatureCoeff_eq_zero_of_far hell (Or.inl hfar))
    · by_contra h
      have hfar : (3/2:ℝ)+ell ≤ y := by dsimp [b] at h ⊢; linarith
      exact hne (bflatQ3FeatureCoeff_eq_zero_of_far hell (Or.inr hfar))
  exact (hcoeffCont.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport)

private theorem bflatCenteredIcc_shift (f : ℝ → ℝ) :
    (∫ x in Icc (-(1/2:ℝ)) (1/2), f x) =
      ∫ t in (0:ℝ)..1, f (t-1/2) := by
  calc
    _ = ∫ x in (-(1/2:ℝ))..(1/2), f x := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-(1/2:ℝ)) ≤ 1/2)]
    _ = ∫ t in (0:ℝ)..1, f (t-1/2) := by
      symm
      convert (intervalIntegral.integral_comp_add_right (f := f) (-(1/2:ℝ))
        (a := (0:ℝ)) (b := 1)) using 1 <;> norm_num

private theorem bflatDoubleCenteredShift {ell : ℝ} (g : ℝ → ℝ) :
    (∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
      ASDExplicitGamma.q3Cov ((t-s)/ell) * g t * g s) =
    (∫ x in Icc (-(1/2:ℝ)) (1/2), ∫ y in Icc (-(1/2:ℝ)) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/ell) * g (x+1/2) * g (y+1/2)) := by
  let H : ℝ → ℝ → ℝ := fun x y =>
    ASDExplicitGamma.q3Cov ((x-y)/ell) * g (x+1/2) * g (y+1/2)
  have hpoint (t s : ℝ) :
      ASDExplicitGamma.q3Cov ((t-s)/ell) * g t * g s = H (t-1/2) (s-1/2) := by
    dsimp [H]
    rw [show ((t-1/2)-(s-1/2))/ell=(t-s)/ell by ring,
      show (t-1/2)+1/2=t by ring, show (s-1/2)+1/2=s by ring]
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
          H (t-1/2) (s-1/2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply intervalIntegral.integral_congr
      intro s hs
      exact hpoint t s
    _ = ∫ t in (0:ℝ)..1, ∫ y in Icc (-(1/2:ℝ)) (1/2), H (t-1/2) y := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (bflatCenteredIcc_shift (fun y => H (t-1/2) y)).symm
    _ = ∫ x in Icc (-(1/2:ℝ)) (1/2), ∫ y in Icc (-(1/2:ℝ)) (1/2), H x y :=
      (bflatCenteredIcc_shift (fun x => ∫ y in Icc (-(1/2:ℝ)) (1/2), H x y)).symm

private theorem bflatQ3ModeLength_pos_local (j : ℕ) :
    0 < (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) := by
  have h : (0:ℚ) < (3:ℚ)^j := pow_pos (by norm_num) j
  rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  exact_mod_cast (one_div_pos.mpr h)

private theorem bflatQ3Kernel_nonneg_abs_le (x : ℝ) :
    0 ≤ ASDExplicitGamma.q3Kernel x ∧
      |ASDExplicitGamma.q3Kernel x| ≤ Real.sqrt (3003/1024) := by
  rw [ASDExplicitGamma.Model.q3Kernel_eq_positive_part]
  let p := max (1-4*x^2) 0
  have hp0 : 0 ≤ p := le_max_right _ _
  have hp1 : p ≤ 1 := by
    apply max_le_iff.mpr
    constructor <;> nlinarith [sq_nonneg x]
  have hp3 : p^3 ≤ 1 := by
    calc
      p^3 ≤ 1^3 := by gcongr
      _ = 1 := by norm_num
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hp0 3)
  · rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hp0 3))]
    simpa [p] using mul_le_mul_of_nonneg_left hp3 (Real.sqrt_nonneg (3003/1024))

private theorem bflatQ3Feature_abs_le {ell : ℝ} (hell : 0 < ell) (y x : ℝ) :
    |bflatQ3Feature ell y x| ≤ Real.sqrt (3003/1024) / Real.sqrt ell := by
  have hkernel := bflatQ3Kernel_nonneg_abs_le ((x-y)/ell)
  have hkernelUpper : ASDExplicitGamma.q3Kernel ((x-y)/ell) ≤
      Real.sqrt (3003/1024) := by
    rw [← abs_of_nonneg hkernel.1]
    exact hkernel.2
  have hinv : 0 ≤ (Real.sqrt ell)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg ell)
  have hfeature : 0 ≤ bflatQ3Feature ell y x := by
    dsimp [bflatQ3Feature]
    exact mul_nonneg hinv hkernel.1
  rw [abs_of_nonneg hfeature, bflatQ3Feature]
  calc
    (Real.sqrt ell)⁻¹ * ASDExplicitGamma.q3Kernel ((x-y)/ell) ≤
        (Real.sqrt ell)⁻¹ * Real.sqrt (3003/1024) :=
      mul_le_mul_of_nonneg_left hkernelUpper hinv
    _ = Real.sqrt (3003/1024) / Real.sqrt ell := by ring

private noncomputable def bflatSineProfile (ell y : ℝ) : ℝ → ℝ :=
  fun t => bflatQ3Feature ell y (t-1/2)

private noncomputable def bflatSineCoefficient (ell : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1,
    bflatQ3Feature ell y (t-1/2) * Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)

private theorem bflatSineCoefficient_eq_featureCoeff (ell : ℝ) (m : ℕ) (y : ℝ) :
    bflatSineCoefficient ell m y =
      bflatQ3FeatureCoeff ell (fun t => Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)) y := by
  dsimp [bflatSineCoefficient, bflatQ3FeatureCoeff]
  exact (bflatIcc01_eq_interval _).symm

/-- The integrated squared sine coefficient of the normalized q3 feature is the
source q3 sine mode mass. -/
theorem bflatQ3FeatureSineCoeff_sq_integral_eq_mode (j n : ℕ) :
    (∫ y : ℝ, (bflatQ3FeatureCoeff
      (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
      (fun t => Real.sin (Real.pi*((n+1:ℕ):ℝ)*t)) y)^2) =
      ASDExplicitGamma.Numerics.Model.q3ModeSine j n / 2 := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let g : ℝ → ℝ := fun t => Real.sin (Real.pi*((n+1:ℕ):ℝ)*t)
  have hg : Continuous g := by fun_prop
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov ((t-s)/ell) * g t * g s :=
      bflatQ3FeatureCoeff_sq_integral (bflatQ3ModeLength_pos_local j) hg
    _ = ∫ x in Icc (-(1/2:ℝ)) (1/2), ∫ y in Icc (-(1/2:ℝ)) (1/2),
        ASDExplicitGamma.q3Cov ((x-y)/ell) * g (x+1/2) * g (y+1/2) :=
      bflatDoubleCenteredShift g
    _ = ASDExplicitGamma.Numerics.Model.q3ModeSine j n / 2 := by
      convert bflatQ3SineModeIntegral_eq_q3Mode j n using 1 <;> norm_num [ell, g]

private theorem bflatSineCoefficientMass_summable {ell : ℝ} (hell : 0 < ell) :
    Summable (fun m : ℕ => ∫ y : ℝ, (bflatSineCoefficient ell m y)^2) := by
  let E : ℝ → ℝ := fun y => ∫ t in (0:ℝ)..1, (bflatSineProfile ell y t)^2
  let A : ℕ → ℝ := fun m => ∫ y : ℝ, (bflatSineCoefficient ell m y)^2
  have hEnergy : (∫ y : ℝ, E y) = 1 := by
    simpa [E, bflatSineProfile] using bflatQ3FeatureEnergy_integral hell
  have hEnergyInt : Integrable E := integrable_of_integral_eq_one hEnergy
  have hAint (m : ℕ) : Integrable (fun y : ℝ =>
      (bflatSineCoefficient ell m y)^2) := by
    have hbase := bflatQ3FeatureCoeff_sq_integrable hell (by fun_prop :
      Continuous (fun t : ℝ => Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)))
    exact hbase.congr (ae_of_all _ fun y =>
      congrArg (fun z : ℝ => z^2) (bflatSineCoefficient_eq_featureCoeff ell m y).symm)
  have hAnonneg (m : ℕ) : 0 ≤ A m := by
    apply integral_nonneg
    intro y
    exact sq_nonneg _
  have hsumBound (N : ℕ) : ∑ m ∈ Finset.range N, A m ≤ 1/2 := by
    have hfiniteInt : Integrable (fun y : ℝ =>
        ∑ m ∈ Finset.range N, (bflatSineCoefficient ell m y)^2) :=
      integrable_finsetSum (Finset.range N) (fun m hm => hAint m)
    have hrightInt : Integrable (fun y : ℝ => (1/2:ℝ)*E y) := by
      simpa [mul_comm] using hEnergyInt.const_mul (1/2:ℝ)
    have hpoint (y : ℝ) :
        (∑ m ∈ Finset.range N, (bflatSineCoefficient ell m y)^2) ≤
          (1/2:ℝ)*E y := by
      have hfcont : Continuous (bflatSineProfile ell y) := by
        exact (bflatQ3Feature_centered_continuous ell).comp
          (continuous_const.prodMk continuous_id)
      have hbound (t : ℝ) :
          |bflatSineProfile ell y t| ≤ Real.sqrt (3003/1024)/Real.sqrt ell := by
        exact bflatQ3Feature_abs_le hell y (t-1/2)
      have hcoeffSum := bflatSineModeCoefficients_summable hfcont hbound
      have hcoeffSum' : Summable (fun m : ℕ =>
          (bflatSineCoefficient ell m y)^2) := by
        simpa [bflatSineCoefficient, bflatSineProfile] using hcoeffSum
      have hsumle :
          (∑ m ∈ Finset.range N, (bflatSineCoefficient ell m y)^2) ≤
            ∑' m : ℕ, (bflatSineCoefficient ell m y)^2 := by
        exact hcoeffSum'.sum_le_tsum (Finset.range N) (fun m hm => sq_nonneg _)
      have hparseval := bflatSineParsevalInterval hfcont hbound
      have hparseval' : 2*(∑' m : ℕ, (bflatSineCoefficient ell m y)^2) = E y := by
        simpa [E, bflatSineCoefficient, bflatSineProfile] using hparseval
      have htwo : 2*(∑ m ∈ Finset.range N,
          (bflatSineCoefficient ell m y)^2) ≤ E y := by
        calc
          _ ≤ 2*(∑' m : ℕ, (bflatSineCoefficient ell m y)^2) := by
            exact mul_le_mul_of_nonneg_left hsumle (by norm_num)
          _ = E y := hparseval'
      nlinarith [htwo]
    have hmono := integral_mono_ae hfiniteInt hrightInt (ae_of_all _ hpoint)
    rw [integral_finsetSum (Finset.range N) (fun m hm => hAint m)] at hmono
    have htop : (∫ y : ℝ, (1/2:ℝ)*E y) = 1/2 := by
      rw [integral_const_mul, hEnergy]
      norm_num
    rw [htop] at hmono
    exact hmono
  exact summable_of_sum_range_le hAnonneg hsumBound

/-- The q3 sine modes have total mass one. -/
theorem bflatQ3ModeSine_mass_sum (j : ℕ) :
    (∑' m : ℕ, ASDExplicitGamma.Numerics.Model.q3ModeSine j m) = 1 := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let A : ℕ → ℝ := fun m => ∫ y : ℝ, (bflatSineCoefficient ell m y)^2
  have hsumA : Summable A := by
    simpa [A, ell, bflatSineCoefficient] using
      bflatSineCoefficientMass_summable (bflatQ3ModeLength_pos_local j)
  have hFint (m : ℕ) : Integrable (fun y : ℝ =>
      (bflatSineCoefficient ell m y)^2) := by
    have hbase := bflatQ3FeatureCoeff_sq_integrable
      (bflatQ3ModeLength_pos_local j) (by fun_prop :
        Continuous (fun t : ℝ => Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)))
    exact hbase.congr (ae_of_all _ fun y =>
      congrArg (fun z : ℝ => z^2) (bflatSineCoefficient_eq_featureCoeff ell m y).symm)
  have hnorm (m : ℕ) :
      (∫ y : ℝ, ‖(bflatSineCoefficient ell m y)^2‖) = A m := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsumNorm : Summable (fun m : ℕ =>
      ∫ y : ℝ, ‖(bflatSineCoefficient ell m y)^2‖) :=
    hsumA.congr (fun m => (hnorm m).symm)
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumNorm
  have hEnergy : (∫ y : ℝ, ∫ t in (0:ℝ)..1,
      (bflatQ3Feature ell y (t-1/2))^2) = 1 := by
    exact bflatQ3FeatureEnergy_integral (bflatQ3ModeLength_pos_local j)
  have hparseval (y : ℝ) :
      2 * (∑' m : ℕ, (bflatSineCoefficient ell m y)^2) =
        ∫ t in (0:ℝ)..1, (bflatQ3Feature ell y (t-1/2))^2 := by
    have hfcont : Continuous (bflatSineProfile ell y) := by
      exact (bflatQ3Feature_centered_continuous ell).comp
        (continuous_const.prodMk continuous_id)
    have hbound (t : ℝ) :
        |bflatSineProfile ell y t| ≤ Real.sqrt (3003/1024)/Real.sqrt ell :=
      bflatQ3Feature_abs_le (bflatQ3ModeLength_pos_local j) y (t-1/2)
    simpa [bflatSineCoefficient, bflatSineProfile] using
      bflatSineParsevalInterval hfcont hbound
  have hmass : (∑' m : ℕ, A m) = 1/2 := by
    calc
      _ = ∫ y : ℝ, ∑' m : ℕ, (bflatSineCoefficient ell m y)^2 := hswap
      _ = ∫ y : ℝ, (1/2:ℝ) *
          (∫ t in (0:ℝ)..1, (bflatQ3Feature ell y (t-1/2))^2) := by
        apply integral_congr_ae
        filter_upwards [] with y
        have hp := hparseval y
        nlinarith [hp]
      _ = 1/2 := by rw [integral_const_mul, hEnergy]; norm_num
  have hmode (m : ℕ) :
      ASDExplicitGamma.Numerics.Model.q3ModeSine j m = 2*A m := by
    have h := bflatQ3FeatureSineCoeff_sq_integral_eq_mode j m
    have hAeq : A m = ∫ y : ℝ,
        (bflatQ3FeatureCoeff ell
          (fun t => Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)) y)^2 := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact congrArg (fun z : ℝ => z^2) (bflatSineCoefficient_eq_featureCoeff ell m y)
    have hmass' : A m = ASDExplicitGamma.Numerics.Model.q3ModeSine j m / 2 := by
      rw [hAeq]
      simpa [ell] using h
    nlinarith [hmass']
  calc
    _ = ∑' m : ℕ, 2*A m := tsum_congr hmode
    _ = 2 * ∑' m : ℕ, A m := by rw [tsum_mul_left]
    _ = 1 := by rw [hmass]; norm_num

private noncomputable def bflatCosineCoefficient (ell : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1,
    bflatQ3Feature ell y (t-1/2) * Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)

private noncomputable def bflatCosineConstantCoefficient (ell y : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, bflatQ3Feature ell y (t-1/2)

private theorem bflatCosineCoefficient_eq_featureCoeff (ell : ℝ) (m : ℕ) (y : ℝ) :
    bflatCosineCoefficient ell m y =
      bflatQ3FeatureCoeff ell (fun t => Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)) y := by
  dsimp [bflatCosineCoefficient, bflatQ3FeatureCoeff]
  exact (bflatIcc01_eq_interval _).symm

private theorem bflatCosineConstant_eq_featureCoeff (ell y : ℝ) :
    bflatCosineConstantCoefficient ell y =
      bflatQ3FeatureCoeff ell (fun _ : ℝ => 1) y := by
  dsimp [bflatCosineConstantCoefficient, bflatQ3FeatureCoeff]
  simpa [mul_one] using (bflatIcc01_eq_interval
    (fun t => bflatQ3Feature ell y (t-1/2))).symm

/-- The integrated squared cosine coefficient of the normalized q3 feature is the
source q3 cosine mode mass. -/
theorem bflatQ3FeatureCosineCoeff_sq_integral_eq_mode (j n : ℕ) :
    (∫ y : ℝ, (bflatQ3FeatureCoeff
      (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
      (fun t => Real.cos (Real.pi*((n+1:ℕ):ℝ)*t)) y)^2) =
      ASDExplicitGamma.Numerics.Model.q3ModeCosine j n / 2 := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let g : ℝ → ℝ := fun t => Real.cos (Real.pi*((n+1:ℕ):ℝ)*t)
  have hg : Continuous g := by fun_prop
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov ((t-s)/ell) * g t * g s :=
      bflatQ3FeatureCoeff_sq_integral (bflatQ3ModeLength_pos_local j) hg
    _ = ∫ x in Icc (-(1/2:ℝ)) (1/2), ∫ y in Icc (-(1/2:ℝ)) (1/2),
        ASDExplicitGamma.q3Cov ((x-y)/ell) * g (x+1/2) * g (y+1/2) :=
      bflatDoubleCenteredShift g
    _ = ASDExplicitGamma.Numerics.Model.q3ModeCosine j n / 2 := by
      convert bflatQ3CosineModeIntegral_eq_q3Mode j n using 1 <;> norm_num [ell, g]

/-- The integrated squared constant coefficient of the normalized q3 feature is the
one-dimensional q3 constant-mode mass. -/
theorem bflatQ3FeatureConstantCoeff_sq_integral (j : ℕ) :
    (∫ y : ℝ,
      (bflatQ3FeatureCoeff (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
        (fun _ : ℝ => 1) y)^2) =
      (429/700:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) -
        (7/60:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)^2 := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  have hell : 0 < ell := bflatQ3ModeLength_pos_local j
  have hell1 : ell ≤ 1 := by
    have hp : ∀ n : ℕ, (1:ℚ) ≤ 3^n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih => rw [pow_succ]; nlinarith
    have hq : ASDExplicitGamma.Numerics.Model.q3ModeLength j ≤ 1 := by
      rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
      have hd : (0:ℚ) < 3^j := pow_pos (by norm_num) j
      exact (div_le_iff₀ hd).2 (by simpa using hp j)
    have hreal : (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) ≤ 1 := by
      exact_mod_cast hq
    simpa [ell] using hreal
  have hconst : Continuous (fun _ : ℝ => (1:ℝ)) := continuous_const
  calc
    _ = ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov ((t-s)/ell) := by
      simpa [ell] using (bflatQ3FeatureCoeff_sq_integral hell hconst)
    _ = ∫ x in Icc (-(1/2:ℝ)) (1/2), ∫ y in Icc (-(1/2:ℝ)) (1/2),
        ASDExplicitGamma.q3Cov ((x-y)/ell) := by
      convert bflatDoubleCenteredShift (ell := ell) (fun _ : ℝ => (1:ℝ)) using 1 <;> norm_num
    _ = 2*ell*(∫ u in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov u*(1-ell*u)) :=
      by convert bflatQ3ConstantModeIntegral ell hell hell1 using 1 <;> norm_num
    _ = (429/700:ℝ)*ell-(7/60:ℝ)*ell^2 := q3Cov_flat_constant_mode ell

private theorem bflatCosineCoefficientMass_summable {ell : ℝ} (hell : 0 < ell) :
    Summable (fun m : ℕ => ∫ y : ℝ, (bflatCosineCoefficient ell m y)^2) := by
  let E : ℝ → ℝ := fun y => ∫ t in (0:ℝ)..1, (bflatSineProfile ell y t)^2
  let A : ℕ → ℝ := fun m => ∫ y : ℝ, (bflatCosineCoefficient ell m y)^2
  have hEnergy : (∫ y : ℝ, E y) = 1 := by
    simpa [E, bflatSineProfile] using bflatQ3FeatureEnergy_integral hell
  have hEnergyInt : Integrable E := integrable_of_integral_eq_one hEnergy
  have hAint (m : ℕ) : Integrable (fun y : ℝ =>
      (bflatCosineCoefficient ell m y)^2) := by
    have hbase := bflatQ3FeatureCoeff_sq_integrable hell (by fun_prop :
      Continuous (fun t : ℝ => Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)))
    exact hbase.congr (ae_of_all _ fun y =>
      congrArg (fun z : ℝ => z^2) (bflatCosineCoefficient_eq_featureCoeff ell m y).symm)
  have hAnonneg (m : ℕ) : 0 ≤ A m := by
    apply integral_nonneg
    intro y
    exact sq_nonneg _
  have hsumBound (N : ℕ) : ∑ m ∈ Finset.range N, A m ≤ 1/2 := by
    have hfiniteInt : Integrable (fun y : ℝ =>
        ∑ m ∈ Finset.range N, (bflatCosineCoefficient ell m y)^2) :=
      integrable_finsetSum (Finset.range N) (fun m hm => hAint m)
    have hrightInt : Integrable (fun y : ℝ => (1/2:ℝ)*E y) := by
      simpa [mul_comm] using hEnergyInt.const_mul (1/2:ℝ)
    have hpoint (y : ℝ) :
        (∑ m ∈ Finset.range N, (bflatCosineCoefficient ell m y)^2) ≤
          (1/2:ℝ)*E y := by
      have hfcont : Continuous (bflatSineProfile ell y) := by
        exact (bflatQ3Feature_centered_continuous ell).comp
          (continuous_const.prodMk continuous_id)
      have hbound (t : ℝ) :
          |bflatSineProfile ell y t| ≤ Real.sqrt (3003/1024)/Real.sqrt ell :=
        bflatQ3Feature_abs_le hell y (t-1/2)
      have hcoeffSum := bflatCosineModeCoefficients_summable hfcont hbound
      have hcoeffSum' : Summable (fun m : ℕ =>
          (bflatCosineCoefficient ell m y)^2) := by
        simpa [bflatCosineCoefficient, bflatSineProfile] using hcoeffSum
      have hsumle :
          (∑ m ∈ Finset.range N, (bflatCosineCoefficient ell m y)^2) ≤
            ∑' m : ℕ, (bflatCosineCoefficient ell m y)^2 :=
        hcoeffSum'.sum_le_tsum (Finset.range N) (fun m hm => sq_nonneg _)
      have hparseval := bflatCosineParsevalInterval hfcont hbound
      have hparseval' :
          (∫ t in (0:ℝ)..1, bflatCosineConstantCoefficient ell y)^2 +
            2*(∑' m : ℕ, (bflatCosineCoefficient ell m y)^2) = E y := by
        simpa [E, bflatCosineCoefficient, bflatCosineConstantCoefficient,
          bflatSineProfile] using hparseval
      have htwo : 2*(∑ m ∈ Finset.range N,
          (bflatCosineCoefficient ell m y)^2) ≤ E y := by
        calc
          _ ≤ 2*(∑' m : ℕ, (bflatCosineCoefficient ell m y)^2) :=
            mul_le_mul_of_nonneg_left hsumle (by norm_num)
          _ ≤ E y := by
            have hconst : 0 ≤
                (∫ t in (0:ℝ)..1, bflatCosineConstantCoefficient ell y)^2 :=
              sq_nonneg _
            nlinarith [hparseval', hconst]
      nlinarith [htwo]
    have hmono := integral_mono_ae hfiniteInt hrightInt (ae_of_all _ hpoint)
    rw [integral_finsetSum (Finset.range N) (fun m hm => hAint m)] at hmono
    have htop : (∫ y : ℝ, (1/2:ℝ)*E y) = 1/2 := by
      rw [integral_const_mul, hEnergy]
      norm_num
    rw [htop] at hmono
    exact hmono
  exact summable_of_sum_range_le hAnonneg hsumBound

/-- The q3 cosine modes have total mass equal to one minus the constant-mode mass. -/
theorem bflatQ3ModeCosine_mass_sum (j : ℕ) :
    (∑' m : ℕ, ASDExplicitGamma.Numerics.Model.q3ModeCosine j m) =
      1 - ((429/700:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) -
        (7/60:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)^2) := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let A : ℕ → ℝ := fun m => ∫ y : ℝ, (bflatCosineCoefficient ell m y)^2
  let C0 : ℝ → ℝ := fun y => bflatCosineConstantCoefficient ell y
  have hsumA : Summable A := by
    simpa [A, ell, bflatCosineCoefficient] using
      bflatCosineCoefficientMass_summable (bflatQ3ModeLength_pos_local j)
  have hFint (m : ℕ) : Integrable (fun y : ℝ =>
      (bflatCosineCoefficient ell m y)^2) := by
    have hbase := bflatQ3FeatureCoeff_sq_integrable
      (bflatQ3ModeLength_pos_local j) (by fun_prop :
        Continuous (fun t : ℝ => Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)))
    exact hbase.congr (ae_of_all _ fun y =>
      congrArg (fun z : ℝ => z^2) (bflatCosineCoefficient_eq_featureCoeff ell m y).symm)
  have hnorm (m : ℕ) :
      (∫ y : ℝ, ‖(bflatCosineCoefficient ell m y)^2‖) = A m := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsumNorm : Summable (fun m : ℕ =>
      ∫ y : ℝ, ‖(bflatCosineCoefficient ell m y)^2‖) :=
    hsumA.congr (fun m => (hnorm m).symm)
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumNorm
  have hEnergy : (∫ y : ℝ, ∫ t in (0:ℝ)..1,
      (bflatQ3Feature ell y (t-1/2))^2) = 1 :=
    bflatQ3FeatureEnergy_integral (bflatQ3ModeLength_pos_local j)
  have hconstMass : (∫ y : ℝ, (C0 y)^2) =
      (429/700:ℝ)*ell-(7/60:ℝ)*ell^2 := by
    have hbase := bflatQ3FeatureConstantCoeff_sq_integral j
    have hcoeffEq (y : ℝ) : C0 y =
        bflatQ3FeatureCoeff ell (fun _ : ℝ => 1) y := by
      dsimp [C0, ell]
      exact bflatCosineConstant_eq_featureCoeff _ _
    calc
      _ = ∫ y : ℝ, (bflatQ3FeatureCoeff ell (fun _ : ℝ => 1) y)^2 := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact congrArg (fun z : ℝ => z^2) (hcoeffEq y)
      _ = _ := by simpa [ell] using hbase
  have hconstInt : Integrable (fun y : ℝ => (C0 y)^2) := by
    have hbase := bflatQ3FeatureCoeff_sq_integrable
      (bflatQ3ModeLength_pos_local j) (g := fun _ : ℝ => (1:ℝ)) continuous_const
    exact hbase.congr (ae_of_all _ fun y =>
      congrArg (fun z : ℝ => z^2) (bflatCosineConstant_eq_featureCoeff ell y).symm)
  have hparseval (y : ℝ) :
      (C0 y)^2 + 2*(∑' m : ℕ, (bflatCosineCoefficient ell m y)^2) =
        ∫ t in (0:ℝ)..1, (bflatQ3Feature ell y (t-1/2))^2 := by
    have hfcont : Continuous (bflatSineProfile ell y) := by
      exact (bflatQ3Feature_centered_continuous ell).comp
        (continuous_const.prodMk continuous_id)
    have hbound (t : ℝ) :
        |bflatSineProfile ell y t| ≤ Real.sqrt (3003/1024)/Real.sqrt ell :=
      bflatQ3Feature_abs_le (bflatQ3ModeLength_pos_local j) y (t-1/2)
    simpa [C0, bflatCosineConstantCoefficient, bflatCosineCoefficient,
      bflatSineProfile] using bflatCosineParsevalInterval hfcont hbound
  have hmass : (∑' m : ℕ, A m) =
      (1-((429/700:ℝ)*ell-(7/60:ℝ)*ell^2))/2 := by
    calc
      _ = ∫ y : ℝ, ∑' m : ℕ, (bflatCosineCoefficient ell m y)^2 := hswap
      _ = ∫ y : ℝ, (1/2:ℝ)*(∫ t in (0:ℝ)..1,
            (bflatQ3Feature ell y (t-1/2))^2) - (1/2:ℝ)*(C0 y)^2 := by
        apply integral_congr_ae
        filter_upwards [] with y
        have hp := hparseval y
        nlinarith [hp]
      _ = (1-((429/700:ℝ)*ell-(7/60:ℝ)*ell^2))/2 := by
        have hfirstInt : Integrable (fun y : ℝ =>
            (1/2:ℝ)*(∫ t in (0:ℝ)..1, (bflatQ3Feature ell y (t-1/2))^2)) := by
          have hi := integrable_of_integral_eq_one hEnergy
          simpa [mul_comm] using hi.const_mul (1/2:ℝ)
        have hsecondInt : Integrable (fun y : ℝ => (1/2:ℝ)*(C0 y)^2) := by
          simpa [mul_comm] using hconstInt.const_mul (1/2:ℝ)
        rw [integral_sub hfirstInt hsecondInt, integral_const_mul, hEnergy,
          integral_const_mul, hconstMass]
        ring
  have hmode (m : ℕ) :
      ASDExplicitGamma.Numerics.Model.q3ModeCosine j m = 2*A m := by
    have h := bflatQ3FeatureCosineCoeff_sq_integral_eq_mode j m
    have hAeq : A m = ∫ y : ℝ,
        (bflatQ3FeatureCoeff ell
          (fun t => Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)) y)^2 := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact congrArg (fun z : ℝ => z^2) (bflatCosineCoefficient_eq_featureCoeff ell m y)
    have hmass' : A m = ASDExplicitGamma.Numerics.Model.q3ModeCosine j m / 2 := by
      rw [hAeq]
      simpa [ell] using h
    nlinarith [hmass']
  calc
    _ = ∑' m : ℕ, 2*A m := tsum_congr hmode
    _ = 2 * ∑' m : ℕ, A m := by rw [tsum_mul_left]
    _ = 1 - ((429/700:ℝ)*ell-(7/60:ℝ)*ell^2) := by
      rw [hmass]
      ring

/-- The actual sine covariance masses are summable. -/
theorem bflatQ3ModeSine_summable (j : ℕ) :
    Summable (fun m : ℕ => ASDExplicitGamma.Numerics.Model.q3ModeSine j m) := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let A : ℕ → ℝ := fun m => ∫ y : ℝ, (bflatSineCoefficient ell m y)^2
  have hsumA : Summable A := by
    simpa [A, ell, bflatSineCoefficient] using
      bflatSineCoefficientMass_summable (bflatQ3ModeLength_pos_local j)
  have hmode (m : ℕ) : ASDExplicitGamma.Numerics.Model.q3ModeSine j m = 2*A m := by
    have h := bflatQ3FeatureSineCoeff_sq_integral_eq_mode j m
    have hAeq : A m = ∫ y : ℝ,
        (bflatQ3FeatureCoeff ell
          (fun t => Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)) y)^2 := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact congrArg (fun z : ℝ => z^2) (bflatSineCoefficient_eq_featureCoeff ell m y)
    have hmass : A m = ASDExplicitGamma.Numerics.Model.q3ModeSine j m / 2 := by
      rw [hAeq]
      simpa [ell] using h
    nlinarith [hmass]
  have heq : (fun m : ℕ => ASDExplicitGamma.Numerics.Model.q3ModeSine j m) =
      fun m => 2*A m := funext hmode
  rw [heq]
  exact hsumA.mul_left 2

/-- The actual cosine covariance masses are summable. -/
theorem bflatQ3ModeCosine_summable (j : ℕ) :
    Summable (fun m : ℕ => ASDExplicitGamma.Numerics.Model.q3ModeCosine j m) := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let A : ℕ → ℝ := fun m => ∫ y : ℝ, (bflatCosineCoefficient ell m y)^2
  have hsumA : Summable A := by
    simpa [A, ell, bflatCosineCoefficient] using
      bflatCosineCoefficientMass_summable (bflatQ3ModeLength_pos_local j)
  have hmode (m : ℕ) : ASDExplicitGamma.Numerics.Model.q3ModeCosine j m = 2*A m := by
    have h := bflatQ3FeatureCosineCoeff_sq_integral_eq_mode j m
    have hAeq : A m = ∫ y : ℝ,
        (bflatQ3FeatureCoeff ell
          (fun t => Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)) y)^2 := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact congrArg (fun z : ℝ => z^2) (bflatCosineCoefficient_eq_featureCoeff ell m y)
    have hmass : A m = ASDExplicitGamma.Numerics.Model.q3ModeCosine j m / 2 := by
      rw [hAeq]
      simpa [ell] using h
    nlinarith [hmass]
  have heq : (fun m : ℕ => ASDExplicitGamma.Numerics.Model.q3ModeCosine j m) =
      fun m => 2*A m := funext hmode
  rw [heq]
  exact hsumA.mul_left 2

/-- Both actual modal covariance masses are nonnegative, as their feature-square
representations show. -/
theorem bflatQ3ModeSine_nonneg (j m : ℕ) :
    0 ≤ ASDExplicitGamma.Numerics.Model.q3ModeSine j m := by
  have h := bflatQ3FeatureSineCoeff_sq_integral_eq_mode j m
  have hnonneg : 0 ≤ ∫ y : ℝ,
      (bflatQ3FeatureCoeff (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
        (fun t => Real.sin (Real.pi*((m+1:ℕ):ℝ)*t)) y)^2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [h]

theorem bflatQ3ModeCosine_nonneg (j m : ℕ) :
    0 ≤ ASDExplicitGamma.Numerics.Model.q3ModeCosine j m := by
  have h := bflatQ3FeatureCosineCoeff_sq_integral_eq_mode j m
  have hnonneg : 0 ≤ ∫ y : ℝ,
      (bflatQ3FeatureCoeff (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
        (fun t => Real.cos (Real.pi*((m+1:ℕ):ℝ)*t)) y)^2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [h]

/-- The integrated q3 defect masses total exactly the constant Fourier mass. -/
theorem bflatQ3ModeDifference_mass_sum (j : ℕ) :
    (∑' m : ℕ, ASDExplicitGamma.Numerics.Model.q3ModeDifference j m) =
      (429/700:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) -
        (7/60:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)^2 := by
  have hs := bflatQ3ModeSine_summable j
  have hc := bflatQ3ModeCosine_summable j
  have hsumS := bflatQ3ModeSine_mass_sum j
  have hsumC := bflatQ3ModeCosine_mass_sum j
  calc
    _ = ∑' m : ℕ,
        (ASDExplicitGamma.Numerics.Model.q3ModeSine j m -
          ASDExplicitGamma.Numerics.Model.q3ModeCosine j m) := by
      apply tsum_congr
      intro m
      rfl
    _ = _ := by rw [hs.tsum_sub hc, hsumS, hsumC]; ring

/-- The exact q3 cosine subtraction is its nonnegative sine/cosine defect. -/
theorem bflatQ3ModeDifference_le_sine (j m : ℕ) :
    ASDExplicitGamma.Numerics.Model.q3ModeDifference j m ≤
      ASDExplicitGamma.Numerics.Model.q3ModeSine j m := by
  rw [ASDExplicitGamma.Numerics.Model.q3ModeDifference]
  nlinarith [bflatQ3ModeCosine_nonneg j m]

/-- Parseval and the constant mode give the all-depth q3 modal tail bound. -/
theorem bflatQ3_mode_tail (j : ℕ) :
    2 - 4*(∑' p : ℕ × ℕ,
      ASDExplicitGamma.Numerics.Model.modeWeight p.1 p.2 *
        ((ASDExplicitGamma.Numerics.Model.q3ModeSine j p.1 -
          ASDExplicitGamma.Numerics.Model.q3ModeDifference j p.1) *
          ASDExplicitGamma.Numerics.Model.q3ModeSine j p.2)) ≤
      min 2 ((429/175:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) -
        (7/15:ℝ)*(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)^2) := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  have hs := bflatQ3ModeSine_summable j
  have hd := (hs.sub (bflatQ3ModeCosine_summable j)).congr fun m => by
    rfl
  have hsumS : (∑' m : ℕ, ASDExplicitGamma.Numerics.Model.q3ModeSine j m) = 1 :=
    bflatQ3ModeSine_mass_sum j
  have hsumD : (∑' m : ℕ, ASDExplicitGamma.Numerics.Model.q3ModeDifference j m) =
      2*ell*(∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)) := by
    calc
      _ = (429/700:ℝ)*ell-(7/60:ℝ)*ell^2 := by
        simpa [ell] using bflatQ3ModeDifference_mass_sum j
      _ = 2*ell*(∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)) :=
        (q3Cov_flat_constant_mode ell).symm
  have htail := bflat_q3_modal_tail_bound
    (s := fun m => ASDExplicitGamma.Numerics.Model.q3ModeSine j m)
    (d := fun m => ASDExplicitGamma.Numerics.Model.q3ModeDifference j m)
    (ell := ell) hs hd
    (fun m => bflatQ3ModeSine_nonneg j m)
    (fun m => q3ModeDifference_nonneg j m)
    (fun m => bflatQ3ModeDifference_le_sine j m)
    hsumS hsumD
  simpa [ell] using htail

end ASDExplicitGamma.Model
