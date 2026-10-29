module

public import ASDExplicitGamma.Model.BflatFourierParseval
public import ASDExplicitGamma.Model.BflatModeTransforms
public import ASDExplicitGamma.Model.Q3Kernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Integrated one-dimensional Fourier masses of q3 features -/

@[expose] public section

open MeasureTheory Set

namespace ASDExplicitGamma.Model

private theorem bflat_q3Kernel_even (x : ℝ) :
    ASDExplicitGamma.q3Kernel (-x) = ASDExplicitGamma.q3Kernel x := by
  rw [ASDExplicitGamma.q3Kernel, ASDExplicitGamma.q3Kernel]
  simp only [abs_neg, neg_sq]

noncomputable def bflatQ3Feature (ell y x : ℝ) : ℝ :=
  (Real.sqrt ell)⁻¹ * ASDExplicitGamma.q3Kernel ((x-y)/ell)

theorem bflatQ3Feature_continuous (ell : ℝ) :
    Continuous (fun p : ℝ × ℝ => bflatQ3Feature ell p.1 p.2) := by
  have harg : Continuous (fun p : ℝ × ℝ => (p.2-p.1)/ell) := by fun_prop
  dsimp [bflatQ3Feature]
  exact continuous_const.mul (ASDExplicitGamma.Model.q3Kernel_continuous.comp harg)

theorem bflatQ3Feature_centered_continuous (ell : ℝ) :
    Continuous (fun p : ℝ × ℝ => bflatQ3Feature ell p.1 (p.2-1/2)) := by
  exact (bflatQ3Feature_continuous ell).comp
    (continuous_fst.prodMk (continuous_snd.sub continuous_const))

/-- Integrating two normalized q3 kernel features over their white-noise coordinate
recovers the scaled q3 covariance. -/
theorem bflatQ3Feature_covariance {ell : ℝ} (hell : 0 < ell) (x z : ℝ) :
    (∫ y : ℝ, bflatQ3Feature ell y x * bflatQ3Feature ell y z) =
      ASDExplicitGamma.q3Cov ((x-z)/ell) := by
  let d : ℝ := (x-z)/ell
  let g : ℝ → ℝ := fun u => ASDExplicitGamma.q3Kernel u *
    ASDExplicitGamma.q3Kernel (u+d)
  have hsquare : (Real.sqrt ell)⁻¹ * (Real.sqrt ell)⁻¹ = ell⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hell.le]
  have hpoint (y : ℝ) :
      bflatQ3Feature ell y x * bflatQ3Feature ell y z =
        ell⁻¹ * g ((y-x)/ell) := by
    dsimp [bflatQ3Feature, g]
    rw [show (x-y)/ell = -((y-x)/ell) by ring,
      bflat_q3Kernel_even,
      show (z-y)/ell = -(d+(y-x)/ell) by dsimp [d]; ring,
      bflat_q3Kernel_even]
    calc
      _ = ((Real.sqrt ell)⁻¹ * (Real.sqrt ell)⁻¹) *
          (ASDExplicitGamma.q3Kernel ((y-x)/ell) *
            ASDExplicitGamma.q3Kernel (d+(y-x)/ell)) := by ring
      _ = ell⁻¹ * (ASDExplicitGamma.q3Kernel ((y-x)/ell) *
          ASDExplicitGamma.q3Kernel ((y-x)/ell+d)) := by
        rw [hsquare, add_comm d ((y-x)/ell)]
  have htrans :
      (∫ y : ℝ, g ((y-x)/ell)) = ∫ y : ℝ, g (y/ell) := by
    have h := (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) (-x)).integral_comp
      (Homeomorph.addRight (-x)).measurableEmbedding (fun y : ℝ => g (y/ell))
    simpa [sub_eq_add_neg, add_comm] using h
  calc
    _ = ∫ y : ℝ, ell⁻¹ * g ((y-x)/ell) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hpoint y
    _ = ell⁻¹ * ∫ y : ℝ, g ((y-x)/ell) := by rw [integral_const_mul]
    _ = ell⁻¹ * ∫ y : ℝ, g (y/ell) := by rw [htrans]
    _ = ell⁻¹ * (ell * ∫ y : ℝ, g y) := by
      rw [MeasureTheory.Measure.integral_comp_div]
      simp [abs_of_pos hell, smul_eq_mul]
    _ = ∫ y : ℝ, g y := by field_simp [ne_of_gt hell]
    _ = ASDExplicitGamma.q3Cov d := by rfl

noncomputable def bflatQ3FeatureCoeff (ell : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in Icc (0:ℝ) 1, bflatQ3Feature ell y (t-1/2) * g t

theorem bflatQ3Feature_zero_left {ell x y : ℝ} (hell : 0 < ell)
    (hx : x ∈ Icc (-(1/2:ℝ)) (1/2)) (hy : y ≤ -(1/2:ℝ)-ell) :
    bflatQ3Feature ell y x = 0 := by
  have hnum : ell ≤ x-y := by nlinarith [hx.1]
  have hratio : 1 ≤ |(x-y)/ell| := by
    rw [abs_of_nonneg (div_nonneg (by linarith [hx.1, hy]) hell.le)]
    apply (le_div_iff₀ hell).2
    nlinarith
  dsimp [bflatQ3Feature]
  rw [ASDExplicitGamma.Model.q3Kernel_eq_zero_of_abs_ge
    (le_trans (by norm_num : (1/2:ℝ) ≤ 1) hratio)]
  ring

theorem bflatQ3Feature_zero_right {ell x y : ℝ} (hell : 0 < ell)
    (hx : x ∈ Icc (-(1/2:ℝ)) (1/2)) (hy : (1/2:ℝ)+ell ≤ y) :
    bflatQ3Feature ell y x = 0 := by
  have hnum : ell ≤ y-x := by nlinarith [hx.2]
  have hratio : 1 ≤ |(x-y)/ell| := by
    rw [show (x-y)/ell = -((y-x)/ell) by ring, abs_neg,
      abs_of_nonneg (div_nonneg (by linarith [hx.2, hy]) hell.le)]
    apply (le_div_iff₀ hell).2
    nlinarith
  dsimp [bflatQ3Feature]
  rw [ASDExplicitGamma.Model.q3Kernel_eq_zero_of_abs_ge
    (le_trans (by norm_num : (1/2:ℝ) ≤ 1) hratio)]
  ring

private theorem bflat_intervalCoeff_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ x in Icc (0:ℝ) 1, f x) = ∫ x in (0:ℝ)..1, f x := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

/-- A feature coefficient vanishes when its white-noise coordinate lies outside the
uniform compact support of the square observation. -/
theorem bflatQ3FeatureCoeff_eq_zero_of_far {ell : ℝ} (hell : 0 < ell)
    {g : ℝ → ℝ} {y : ℝ}
    (hy : y ≤ -(3/2:ℝ)-ell ∨ (3/2:ℝ)+ell ≤ y) :
    bflatQ3FeatureCoeff ell g y = 0 := by
  unfold bflatQ3FeatureCoeff
  let μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
  change (∫ t, bflatQ3Feature ell y (t-1/2) * g t ∂μ) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hcenter : t-1/2 ∈ Icc (-(1/2:ℝ)) (1/2) := by
    constructor <;> linarith [ht.1, ht.2]
  rcases hy with hy | hy
  · have hthreshold : y ≤ -(1/2:ℝ)-ell := by linarith
    rw [bflatQ3Feature_zero_left hell hcenter hthreshold]
    simp
  · have hthreshold : (1/2:ℝ)+ell ≤ y := by linarith
    rw [bflatQ3Feature_zero_right hell hcenter hthreshold]
    simp

/-- The integrated square of a q3 feature coefficient is its covariance quadratic form. -/
theorem bflatQ3FeatureCoeff_sq_integral {ell : ℝ} (hell : 0 < ell)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ y : ℝ, (bflatQ3FeatureCoeff ell g y)^2) =
      ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov ((t-s)/ell) * g t * g s := by
  let H : ℝ → ℝ → ℝ → ℝ := fun y t s =>
    bflatQ3Feature ell y (t-1/2) * g t *
      (bflatQ3Feature ell y (s-1/2) * g s)
  have hHcont : Continuous (fun p : (ℝ×ℝ)×ℝ => H p.1.1 p.1.2 p.2) := by
    dsimp [H]
    have hleft : Continuous (fun p : (ℝ×ℝ)×ℝ =>
        bflatQ3Feature ell p.1.1 (p.1.2-1/2)) :=
      bflatQ3Feature_centered_continuous ell |>.comp continuous_fst
    have hgt : Continuous (fun p : (ℝ×ℝ)×ℝ => g p.1.2) :=
      hg.comp (continuous_snd.comp continuous_fst)
    have hrightMap : Continuous (fun p : (ℝ×ℝ)×ℝ =>
        (p.1.1, p.2)) := by
      exact (continuous_fst.comp continuous_fst).prodMk
        continuous_snd
    have hright : Continuous (fun p : (ℝ×ℝ)×ℝ =>
        bflatQ3Feature ell p.1.1 (p.2-1/2)) :=
      bflatQ3Feature_centered_continuous ell |>.comp hrightMap
    have hgs : Continuous (fun p : (ℝ×ℝ)×ℝ => g p.2) :=
      hg.comp continuous_snd
    exact (hleft.mul hgt).mul (hright.mul hgs)
  let K : ℝ → ℝ → ℝ := fun y t => ∫ s in Icc (0:ℝ) 1, H y t s
  have hKcont : Continuous (Function.uncurry K) := by
    change Continuous (fun p : ℝ×ℝ => ∫ s in Icc (0:ℝ) 1, H p.1 p.2 s)
    have hparam : Continuous (Function.uncurry
        (fun p : ℝ×ℝ => fun s => H p.1 p.2 s)) := by
      change Continuous (fun p : (ℝ×ℝ)×ℝ => H p.1.1 p.1.2 p.2)
      exact hHcont
    exact continuous_parametric_integral_of_continuous hparam isCompact_Icc
  have hcoeff_zero (y : ℝ)
      (hy : y ≤ -(3/2:ℝ)-ell ∨ (3/2:ℝ)+ell ≤ y) :
      bflatQ3FeatureCoeff ell g y = 0 := by
    unfold bflatQ3FeatureCoeff
    let μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
    change (∫ t, bflatQ3Feature ell y (t-1/2) * g t ∂μ) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hcenter : t-1/2 ∈ Icc (-(1/2:ℝ)) (1/2) := by constructor <;> linarith [ht.1, ht.2]
    rcases hy with hy | hy
    · have hthreshold : y ≤ -(1/2:ℝ)-ell := by linarith
      rw [bflatQ3Feature_zero_left hell hcenter hthreshold]
      simp
    · have hthreshold : (1/2:ℝ)+ell ≤ y := by linarith
      rw [bflatQ3Feature_zero_right hell hcenter hthreshold]
      simp
  have hcoeffsq_support :
      Function.support (fun y => (bflatQ3FeatureCoeff ell g y)^2) ⊆
        Ioc (-(3/2:ℝ)-ell) ((3/2:ℝ)+ell) := by
    intro y hy
    have hne : bflatQ3FeatureCoeff ell g y ≠ 0 := by
      intro hz
      apply hy
      simp [hz]
    constructor
    · by_contra h
      exact hne (hcoeff_zero y (Or.inl (le_of_not_gt h)))
    · by_contra h
      exact hne (hcoeff_zero y (Or.inr (le_of_not_ge h)))
  have hfull :
      (∫ y : ℝ, (bflatQ3FeatureCoeff ell g y)^2) =
        ∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell),
          (bflatQ3FeatureCoeff ell g y)^2 :=
    (intervalIntegral.integral_eq_integral_of_support_subset hcoeffsq_support).symm
  have hpair (y : ℝ) :
      (bflatQ3FeatureCoeff ell g y)^2 =
        ∫ t in (0:ℝ)..1, K y t := by
    let μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
    have hFcont : Continuous (fun t : ℝ =>
        bflatQ3Feature ell y (t-1/2) * g t) := by
      exact ((bflatQ3Feature_centered_continuous ell).comp
        (continuous_const.prodMk continuous_id)).mul hg
    have hprodInt : IntegrableOn
        (fun p : ℝ×ℝ =>
          (bflatQ3Feature ell y (p.1-1/2) * g p.1) *
            (bflatQ3Feature ell y (p.2-1/2) * g p.2))
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (volume.prod volume) := by
      have hprod : Continuous (Function.uncurry (fun t s =>
          (bflatQ3Feature ell y (t-1/2) * g t) *
            (bflatQ3Feature ell y (s-1/2) * g s))) := by
        exact hFcont.comp continuous_fst |>.mul
          (hFcont.comp continuous_snd)
      exact hprod.continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    calc
      _ = (∫ t in Icc (0:ℝ) 1, bflatQ3Feature ell y (t-1/2)*g t) *
          (∫ s in Icc (0:ℝ) 1, bflatQ3Feature ell y (s-1/2)*g s) := by
            simp [bflatQ3FeatureCoeff, pow_two]
      _ = ∫ p in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,
          (bflatQ3Feature ell y (p.1-1/2)*g p.1) *
            (bflatQ3Feature ell y (p.2-1/2)*g p.2) ∂(volume.prod volume) := by
            symm
            exact setIntegral_prod_mul
              (fun t => bflatQ3Feature ell y (t-1/2)*g t)
              (fun s => bflatQ3Feature ell y (s-1/2)*g s)
              (Icc (0:ℝ) 1) (Icc (0:ℝ) 1)
      _ = ∫ t in Icc (0:ℝ) 1, ∫ s in Icc (0:ℝ) 1, H y t s :=
            setIntegral_prod _ hprodInt
      _ = ∫ t in (0:ℝ)..1, K y t := by
            rw [bflat_intervalCoeff_eq_intervalIntegral]
  rw [hfull]
  simp_rw [hpair]
  have hKswap : Continuous (Function.uncurry (fun t y => K y t)) := by
    exact hKcont.comp (continuous_snd.prodMk continuous_fst)
  have hKswapInt : IntegrableOn (Function.uncurry (fun t y => K y t))
      (uIoc (0:ℝ) 1 ×ˢ uIoc (-(3/2:ℝ)-ell) ((3/2:ℝ)+ell)) volume := by
    let R : Set (ℝ×ℝ) :=
      uIcc (0:ℝ) 1 ×ˢ uIcc (-(3/2:ℝ)-ell) ((3/2:ℝ)+ell)
    have hcompact : IsCompact R := by
      exact isCompact_uIcc.prod isCompact_uIcc
    have hclosed : IntegrableOn (Function.uncurry (fun t y => K y t)) R volume :=
      hKswap.continuousOn.integrableOn_compact (μ := volume) hcompact
    exact hclosed.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [← intervalIntegral_intervalIntegral_swap hKswapInt]
  have hswapInner (t : ℝ) :
      (∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell), K y t) =
        ∫ s in (0:ℝ)..1,
          (∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell), H y t s) := by
    calc
      _ = ∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell),
          ∫ s in (0:ℝ)..1, H y t s := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact bflat_intervalCoeff_eq_intervalIntegral (H y t)
      _ = _ := intervalIntegral_intervalIntegral_swap (by
        have hHfixed : Continuous (Function.uncurry (fun y s => H y t s)) := by
          dsimp [H]
          have hleftFixed : Continuous (fun p : ℝ×ℝ =>
              bflatQ3Feature ell p.1 (t-1/2)) :=
            (bflatQ3Feature_continuous ell).comp
              (continuous_fst.prodMk continuous_const)
          have hrightFixed : Continuous (fun p : ℝ×ℝ =>
              bflatQ3Feature ell p.1 (p.2-1/2)) :=
            bflatQ3Feature_centered_continuous ell
          have hgsFixed : Continuous (fun p : ℝ×ℝ => g p.2) :=
            hg.comp continuous_snd
          exact (hleftFixed.mul continuous_const).mul (hrightFixed.mul hgsFixed)
        let R : Set (ℝ×ℝ) :=
          uIcc (-(3/2:ℝ)-ell) ((3/2:ℝ)+ell) ×ˢ uIcc (0:ℝ) 1
        have hcompact : IsCompact R := by
          exact isCompact_uIcc.prod isCompact_uIcc
        have hclosed : IntegrableOn (Function.uncurry (fun y s => H y t s)) R volume :=
          hHfixed.continuousOn.integrableOn_compact (μ := volume) hcompact
        exact hclosed.mono_set
          (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
  calc
    _ = ∫ t in (0:ℝ)..1,
        ∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell), K y t := by
          rfl
    _ = ∫ t in (0:ℝ)..1,
        ∫ s in (0:ℝ)..1,
          ∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell), H y t s := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact hswapInner t
    _ = ∫ t in (0:ℝ)..1, ∫ s in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov ((t-s)/ell) * g t * g s := by
          apply intervalIntegral.integral_congr
          intro t ht
          apply intervalIntegral.integral_congr
          intro s hs
          have htcc : t ∈ Icc (0:ℝ) 1 := by
            simpa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
          have hscc : s ∈ Icc (0:ℝ) 1 := by
            simpa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs
          have hcov :
              (∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell),
                bflatQ3Feature ell y (t-1/2) * bflatQ3Feature ell y (s-1/2)) =
                ASDExplicitGamma.q3Cov ((t-s)/ell) := by
            have hcents : t-1/2 ∈ Icc (-(1/2:ℝ)) (1/2) ∧
                s-1/2 ∈ Icc (-(1/2:ℝ)) (1/2) := by
              constructor <;> constructor <;> linarith [htcc.1, htcc.2, hscc.1, hscc.2]
            have hsupp : Function.support (fun y =>
                bflatQ3Feature ell y (t-1/2) * bflatQ3Feature ell y (s-1/2)) ⊆
                Ioc (-(3/2:ℝ)-ell) ((3/2:ℝ)+ell) := by
              intro y hy
              constructor
              · by_contra h
                apply hy
                have hy' : y ≤ -(1/2:ℝ)-ell := by linarith [le_of_not_gt h]
                have hz := bflatQ3Feature_zero_left hell hcents.1 hy'
                exact mul_eq_zero.mpr
                  (Or.inl (by simpa only [one_div] using hz))
              · by_contra h
                apply hy
                have hy' : (1/2:ℝ)+ell ≤ y := by linarith [lt_of_not_ge h]
                have hz := bflatQ3Feature_zero_right hell hcents.1 hy'
                exact mul_eq_zero.mpr
                  (Or.inl (by simpa only [one_div] using hz))
            rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]
            simpa only [show (t-1/2-(s-1/2))/ell = (t-s)/ell by ring] using
              bflatQ3Feature_covariance hell (t-1/2) (s-1/2)
          dsimp [H]
          calc
            (∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell),
                bflatQ3Feature ell y (t-1/2) * g t *
                  (bflatQ3Feature ell y (s-1/2) * g s)) =
                ∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell),
                  (g t*g s) *
                    (bflatQ3Feature ell y (t-1/2) * bflatQ3Feature ell y (s-1/2)) := by
              apply intervalIntegral.integral_congr
              intro y hy
              ring
            _ = (g t*g s) * (∫ y in (-(3/2:ℝ)-ell)..((3/2:ℝ)+ell),
                  bflatQ3Feature ell y (t-1/2) * bflatQ3Feature ell y (s-1/2)) := by
              rw [intervalIntegral.integral_const_mul]
            _ = q3Cov ((t-s)/ell) * g t * g s := by rw [hcov]; ring

end ASDExplicitGamma.Model
