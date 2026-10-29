module

public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Inverse.WeightedLocalizationProfileNumerics
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
public import ASDExplicitGamma.Numerics.Inverse.Layers
public import ASDExplicitGamma.Numerics.Inverse.ProfileFirst
public import ASDExplicitGamma.Numerics.Inverse.ProfileGlobal
public import ASDExplicitGamma.Numerics.Inverse.ProfileLocal
public import ASDExplicitGamma.Numerics.Inverse.FullHistory
public import ASDExplicitGamma.Inverse.StoppedRareMomentCertificates
public import ASDExplicitGamma.Inverse.WeightedLocalizationResetSeries
public import ASDExplicitGamma.Gaussian.WaveGateEstimates

/-! Numeric endpoint bounds for the literal root profile. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse
open ASDExplicitGamma.Gaussian

private theorem bank_reset_profile_decay_summable_bound (C N : ℕ) (rate c : ℝ)
    (hN : (N:ℝ) ≤ rate*((C+1:ℕ):ℝ)) (hrate : 0 ≤ rate)
    (hc : 0 ≤ c) (hc1 : c < 1) (hq : (3:ℝ)^(-rate) ≤ c) :
    Summable (fun hk : ℕ × ℕ =>
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) ∧
    (∑' hk : ℕ × ℕ,
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) ≤
        (3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 := by
  let g : ℕ → ℝ := fun n => c^n
  have hgeom : HasSum g (1/(1-c)) := by
    simpa only [g, one_div] using hasSum_geometric_of_lt_one hc hc1
  have hprod := localization_nonnegative_product_hasSum g g
    (fun n => pow_nonneg hc n) (fun n => pow_nonneg hc n) hgeom hgeom
  have hx (hk : ℕ × ℕ) :
      (C+1:ℕ)+hk.1+hk.2 ≤ localizationResetAbscissa C hk.1 hk.2 := by
    rw [localizationResetAbscissa]
    unfold localizationProfileDepth
    omega
  have hterm (hk : ℕ × ℕ) :
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
        (3:ℝ)^(-(N:ℝ))*(g hk.1*g hk.2) := by
    have hcast : (((C+1:ℕ)+hk.1+hk.2:ℕ):ℝ) ≤
        (localizationResetAbscissa C hk.1 hk.2:ℝ) := by exact_mod_cast hx hk
    have hexp : -(rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
        -(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ) := by
      have hsum : (N:ℝ)+hk.1*rate+hk.2*rate ≤
          rate*(localizationResetAbscissa C hk.1 hk.2:ℝ) := by
        have hmore := mul_le_mul_of_nonneg_left hcast hrate
        have hN' : (N:ℝ)+rate*((hk.1+hk.2:ℕ):ℝ) ≤
            rate*((C+1:ℕ):ℝ)+rate*((hk.1+hk.2:ℕ):ℝ) := by
          have hN0 := hN
          push_cast at hN0
          push_cast
          linarith [hN0]
        have hcastsum : ((hk.1+hk.2:ℕ):ℝ) = (hk.1:ℝ)+(hk.2:ℝ) := by norm_num
        rw [hcastsum] at hN'
        push_cast at hmore
        push_cast at hN'
        nlinarith only [hmore, hN']
      nlinarith only [hsum]
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hexp
    have hpowNat (n : ℕ) : (3:ℝ)^(-rate*(n:ℝ)) = ((3:ℝ)^(-rate))^n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hfactor :
        (3:ℝ)^(-(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ)) =
          (3:ℝ)^(-(N:ℝ))*((3:ℝ)^(-rate))^hk.1*((3:ℝ)^(-rate))^hk.2 := by
      calc
        _ = (3:ℝ)^(-(N:ℝ))*(3:ℝ)^(-rate*(hk.1:ℝ))*(3:ℝ)^(-rate*(hk.2:ℝ)) := by
          rw [show -(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ) =
            (-(N:ℝ)+(-rate*(hk.1:ℝ)))+(-rate*(hk.2:ℝ)) by ring]
          rw [Real.rpow_add (by norm_num : (0:ℝ)<3),
            Real.rpow_add (by norm_num : (0:ℝ)<3)]
        _ = _ := by rw [hpowNat, hpowNat]
    have hfactor_le : (3:ℝ)^(-(N:ℝ))*((3:ℝ)^(-rate))^hk.1*((3:ℝ)^(-rate))^hk.2 ≤
        (3:ℝ)^(-(N:ℝ))*(g hk.1*g hk.2) := by
      dsimp [g]
      have hq1 := pow_le_pow_left₀ (by positivity : 0 ≤ (3:ℝ)^(-rate)) hq hk.1
      have hq2 := pow_le_pow_left₀ (by positivity : 0 ≤ (3:ℝ)^(-rate)) hq hk.2
      have hfront : 0 ≤ (3:ℝ)^(-(N:ℝ)) := by positivity
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hq1 hq2 (by positivity) (by positivity)) hfront)
    have hpow' : (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤
        (3:ℝ)^(-(N:ℝ)-rate*(hk.1:ℝ)-rate*(hk.2:ℝ)) := by
      simpa only [neg_mul] using hpow
    exact hpow'.trans (hfactor.trans_le hfactor_le)
  have hsumMajorant : Summable (fun hk : ℕ × ℕ =>
      (3:ℝ)^(-(N:ℝ))*(g hk.1*g hk.2)) := by
    exact hprod.summable.mul_left _
  have hsum : Summable (fun hk : ℕ × ℕ =>
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) :=
    Summable.of_nonneg_of_le (fun hk => by positivity) hterm hsumMajorant
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' hk : ℕ × ℕ, (3:ℝ)^(-(N:ℝ))*(g hk.1*g hk.2) :=
      hsum.tsum_le_tsum hterm hsumMajorant
    _ = (3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 := by
      have hscaled := hprod.mul_left ((3:ℝ)^(-(N:ℝ)))
      rw [hscaled.tsum_eq]
      ring

private theorem bank_sqrt_layer_weight_le_two (k : ℕ) :
    Real.sqrt (bankLayerWeight k) ≤ 2 := by
  have hu : bankLayerWeight k ≤ 4 := by
    cases k with
    | zero => norm_num [bankLayerWeight]
    | succ k =>
      rw [layerWeight_succ]
      have hp : (1/3:ℝ)^(k+2) ≤ 1/9 := by
        calc
          _ ≤ (1/3:ℝ)^2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = _ := by norm_num
      have hsecond : 0 ≤ (1/9:ℝ)^(k+2) := by positivity
      nlinarith
  apply Real.sqrt_le_iff.mpr
  exact ⟨by norm_num, by norm_num at hu ⊢; exact hu⟩

private theorem bank_three_neg_99_le_034 :
    (3:ℝ)^(-(99/100:ℝ)) ≤ 34/100 := by
  have hsmall := inv_three_power_bound (1/100:ℝ) (by norm_num)
    (by norm_num : (11/10:ℝ)*(1/100)<1)
  have hsplit : (3:ℝ)^(-(99/100:ℝ)) =
      (1/3:ℝ)*(3:ℝ)^(1/100:ℝ) := by
    rw [show (-(99/100:ℝ))=(-1:ℝ)+(1/100:ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0:ℝ)<3), Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    norm_num
  rw [hsplit]
  calc
    _ ≤ (1/3:ℝ)*(1000/989) := by nlinarith
    _ ≤ 34/100 := by norm_num

private theorem bank_three_neg_49_le_059 :
    (3:ℝ)^(-(49/100:ℝ)) ≤ 59/100 := by
  have hsmall := inv_three_power_bound (1/100:ℝ) (by norm_num)
    (by norm_num : (11/10:ℝ)*(1/100)<1)
  have hhalf : (3:ℝ)^(-(1/2:ℝ)) ≤ 29/50 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3), ← Real.sqrt_eq_rpow]
    rw [← one_div]
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3))).2
    have hs : 50/29 ≤ Real.sqrt 3 := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num
    nlinarith
  have hsplit : (3:ℝ)^(-(49/100:ℝ)) =
      (3:ℝ)^(-(1/2:ℝ))*(3:ℝ)^(1/100:ℝ) := by
    rw [show (-(49/100:ℝ))=(-(1/2:ℝ))+(1/100:ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0:ℝ)<3)]
  rw [hsplit]
  have hsmall' : (3:ℝ)^(1/100:ℝ) ≤ 1000/989 := by
    norm_num at hsmall ⊢
    exact hsmall
  calc
    _ ≤ (29/50:ℝ)*(1000/989) := mul_le_mul hhalf hsmall' (by positivity) (by positivity)
    _ ≤ 59/100 := by norm_num

private theorem bank_root_matrix_series_bound (γ : ℝ) (_hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) (C N : ℕ)
    (hN : (N:ℝ) ≤ (99/100)*((C+1:ℕ):ℝ)) :
    (∑' hk : ℕ × ℕ,
      Real.sqrt (bankLayerWeight hk.2)*
        (3:ℝ)^(2*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
        (3:ℝ)^(-((localizationResetAbscissa C hk.1 hk.2:ℝ)+1))) ≤
      (2/3:ℝ)*(3:ℝ)^(-(N:ℝ))/(66/100)^2 := by
  let x (hk : ℕ × ℕ) := (localizationResetAbscissa C hk.1 hk.2:ℝ)
  let f : ℕ × ℕ → ℝ := fun hk => Real.sqrt (bankLayerWeight hk.2)*
    (3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(x hk+1))
  let q : ℕ × ℕ → ℝ := fun hk => (2/3:ℝ)*(3:ℝ)^(-(99/100:ℝ)*
    (localizationResetAbscissa C hk.1 hk.2:ℝ))
  have hsmall : 2*γ ≤ (1/100:ℝ) := by nlinarith only [hγ₀]
  have hx (hk : ℕ × ℕ) : 0 ≤ x hk := by
    dsimp [x, localizationResetAbscissa]
    positivity
  have hfq : ∀ hk, f hk ≤ q hk := by
    intro hk
    have hexp : 2*γ*x hk-(x hk+1) ≤ (-(99/100:ℝ))*x hk-1 := by
      nlinarith only [hsmall, hx hk]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤3) hexp
    have hprod : (3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(x hk+1)) =
        (3:ℝ)^(2*γ*x hk-(x hk+1)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
      congr 1
    have htail : (3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(x hk+1)) ≤
        (1/3:ℝ)*(3:ℝ)^(-(99/100:ℝ)*x hk) := by
      calc
        _ = (3:ℝ)^(2*γ*x hk-(x hk+1) : ℝ) := hprod
        _ ≤ (3:ℝ)^((-(99/100:ℝ))*x hk-1) := hpow
        _ = _ := by
          rw [show ((-(99/100:ℝ))*x hk-1)=((-(99/100:ℝ))*x hk)+(-1) by ring,
            Real.rpow_add (by norm_num : (0:ℝ)<3),
            Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
          norm_num
          ring
    dsimp [f, q]
    calc
      _ ≤ 2*((1/3:ℝ)*(3:ℝ)^(-(99/100:ℝ)*x hk)) := by
        calc
          _ = Real.sqrt (bankLayerWeight hk.2) *
              ((3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(x hk+1))) := by ring
          _ ≤ _ := mul_le_mul (bank_sqrt_layer_weight_le_two hk.2) htail
            (by positivity) (by positivity)
      _ = (2/3:ℝ)*(3:ℝ)^(-(99/100:ℝ)*x hk) := by ring
  have hprof := bank_reset_profile_decay_summable_bound C N (99/100:ℝ) (34/100:ℝ)
    hN (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [show (-99/100:ℝ)=-(99/100:ℝ) by ring] using bank_three_neg_99_le_034)
  have hmajorant : Summable q := by
    simpa [q, x] using hprof.1.mul_left (2/3:ℝ)
  have hseries : Summable f :=
    Summable.of_nonneg_of_le (fun hk => by positivity) hfq hmajorant
  change (∑' hk, f hk) ≤ _
  calc
    _ ≤ ∑' hk, q hk := hseries.tsum_le_tsum hfq hmajorant
    _ = (2/3:ℝ)*(∑' hk : ℕ × ℕ,
        (3:ℝ)^(-(99/100:ℝ)*(localizationResetAbscissa C hk.1 hk.2:ℝ))) := by
      rw [tsum_mul_left]
    _ ≤ (2/3:ℝ)*((3:ℝ)^(-(N:ℝ))/(66/100)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ (3:ℝ)^(-(N:ℝ))*(1/(1-(34/100:ℝ)))^2 := hprof.2
        _ = (3:ℝ)^(-(N:ℝ))/(66/100)^2 := by ring
    _ = (2/3:ℝ)*(3:ℝ)^(-(N:ℝ))/(66/100)^2 := by ring

private theorem bank_root_density_series_bound (γ : ℝ) (_hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) (C N : ℕ)
    (hN : (N:ℝ) ≤ (49/100)*((C+1:ℕ):ℝ)) :
    densityResetPowerSum (2*γ) (1/2) C ≤
      (3:ℝ)^(-(N:ℝ))/(41/100)^2 := by
  have hsmall : 2*γ ≤ (1/100:ℝ) := by nlinarith only [hγ₀]
  have hdecay : 2*γ < (1/2:ℝ) := by nlinarith only [hsmall]
  have hsum := density_reset_power_hasSum (2*γ) (1/2) hdecay C
  let x (hk : ℕ × ℕ) := (localizationResetAbscissa C hk.1 hk.2:ℝ)
  let f : ℕ × ℕ → ℝ := fun hk =>
    (3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(1/2:ℝ)*(x hk+1))
  let q : ℕ × ℕ → ℝ := fun hk => (3:ℝ)^(-(49/100:ℝ)*
    (localizationResetAbscissa C hk.1 hk.2:ℝ))
  have hx (hk : ℕ × ℕ) : 0 ≤ x hk := by
    dsimp [x, localizationResetAbscissa]
    positivity
  have hfq : ∀ hk, f hk ≤ q hk := by
    intro hk
    have hexp : 2*γ*x hk-(1/2:ℝ)*(x hk+1) ≤ (-(49/100:ℝ))*x hk := by
      nlinarith only [hsmall, hx hk]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤3) hexp
    have hprod : (3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(1/2:ℝ)*(x hk+1)) =
        (3:ℝ)^(2*γ*x hk-(1/2:ℝ)*(x hk+1)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
      congr 1
      ring
    calc
      f hk = (3:ℝ)^(2*γ*x hk)*(3:ℝ)^(-(1/2:ℝ)*(x hk+1)) := by rfl
      _ = (3:ℝ)^(2*γ*x hk-(1/2:ℝ)*(x hk+1)) := hprod
      _ ≤ q hk := by simpa [q, x, show (-49/100:ℝ)=-(49/100:ℝ) by ring] using hpow
  have hprof := bank_reset_profile_decay_summable_bound C N (49/100:ℝ) (59/100:ℝ)
    hN (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [show (-49/100:ℝ)=-(49/100:ℝ) by ring] using bank_three_neg_49_le_059)
  have hmajorant : Summable q := by
    simpa [q] using hprof.1
  have hseries : Summable f :=
    Summable.of_nonneg_of_le (fun hk => by positivity) hfq hmajorant
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' hk, q hk := hseries.tsum_le_tsum hfq hmajorant
    _ ≤ (3:ℝ)^(-(N:ℝ))/(41/100)^2 := by
      calc
        _ ≤ (3:ℝ)^(-(N:ℝ))*(1/(1-(59/100:ℝ)))^2 := hprof.2
      _ = (3:ℝ)^(-(N:ℝ))/(41/100)^2 := by ring

theorem bank_root_density_power_nonneg (γ : ℝ)
    (hγ₀ : γ ≤ 17/50000) (C : ℕ) :
    0 ≤ densityResetPowerSum (2*γ) (1/2) C := by
  have hdecay : 2*γ < (1/2:ℝ) := by nlinarith only [hγ₀]
  have hs := density_reset_power_hasSum (2*γ) (1/2) hdecay C
  rw [← hs.tsum_eq]
  apply tsum_nonneg
  intro hk
  positivity

theorem bank_root_layer_sum_endpoint (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17 / 50000) :
    rootLayerSum (2 * γ) ≤ (invLayer (2 * invGamma) : ℝ) := by
  let z : ℝ := (3 : ℝ) ^ (2 * γ)
  let z₀ : ℝ := (invE (11 / 10 * 2 * invGamma) : ℚ)
  have hz : 0 ≤ z := by positivity
  have hdom : (11 / 10 : ℝ) * (2 * γ) < 1 := by
    norm_num at hγ₀ ⊢
    nlinarith
  have hpow := inv_three_power_bound (2 * γ) (by positivity) hdom
  have hden₀ : 0 < 1 - (11 / 10 : ℝ) * (2 * (invGamma : ℝ)) := by
    norm_num [invGamma]
  have hγend : γ ≤ (invGamma : ℝ) := by
    norm_num [invGamma] at hγ₀ ⊢
    exact hγ₀
  have hden : 1 - (11 / 10 : ℝ) * (2 * (invGamma : ℝ)) ≤
      1 - (11 / 10 : ℝ) * (2 * γ) := by
    norm_num [invGamma] at hγend ⊢
    nlinarith
  have hzle : z ≤ z₀ := by
    dsimp [z, z₀]
    have hbound : (3 : ℝ) ^ (2 * γ) ≤
        1 / (1 - (11 / 10 : ℝ) * (2 * γ)) := by
      simpa only [one_div] using hpow
    have hrecip' :
        1 / (1 - (11 / 10 : ℝ) * (2 * γ)) ≤
          1 / (1 - (11 / 10 : ℝ) * (2 * (invGamma : ℝ))) := by
      exact one_div_le_one_div_of_le hden₀ hden
    have hfinal := hbound.trans hrecip'
    have hz₀eq : 1 / (1 - (11 / 10 : ℝ) * (2 * (invGamma : ℝ))) =
        (invE (11 / 10 * 2 * invGamma) : ℚ) := by
      norm_num [invE, invGamma]
    exact hfinal.trans_eq hz₀eq
  have hz₀ : 0 ≤ z₀ := by norm_num [z₀, invE, invGamma]
  have hsmall₀ : z₀ ^ 4 < 27 := by norm_num [z₀, invE, invGamma]
  have hsmall : z ^ 4 < 27 :=
    (pow_le_pow_left₀ hz hzle 4).trans_lt hsmall₀
  have hsum := localization_layer_profile_hasSum z hz hsmall
  have hsum₀ := localization_layer_profile_hasSum z₀ hz₀ hsmall₀
  have hterm (n : ℕ) :
      z ^ localizationProfileDepth (n + 1) =
        (3 : ℝ) ^ (2 * γ * (localizationProfileDepth (n + 1) : ℝ)) := by
    dsimp [z]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * γ)) (localizationProfileDepth (n + 1)),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hLayer : rootLayerSum (2 * γ) =
      8 * localizationProfileT (1 / 3) z -
        32 * localizationProfileT (1 / 9) z + z ^ 2 := by
    unfold rootLayerSum
    have heq : (fun n : ℕ => bankLayerWeight n *
        (3 : ℝ) ^ (2 * γ * (localizationProfileDepth (n + 1) : ℝ))) =
        (fun n => bankLayerWeight n * z ^ localizationProfileDepth (n + 1)) := by
      funext n
      rw [hterm]
    rw [heq]
    exact hsum.tsum_eq
  have hprofile := localization_layer_profile_mono hz hzle hsmall₀
  have hprofile₀ :
      8 * localizationProfileT ((1 / 3 : ℚ) : ℝ) z₀ -
        32 * localizationProfileT ((1 / 9 : ℚ) : ℝ) z₀ + z₀ ^ 2 =
          (invExactLayerTwo : ℚ) := by
    dsimp [z₀]
    rw [localization_profileT_numeric (1 / 3 : ℚ) (invE (11 / 10 * 2 * invGamma)),
      localization_profileT_numeric (1 / 9 : ℚ) (invE (11 / 10 * 2 * invGamma))]
    norm_num [invExactLayerTwo]
  have hnum : (invExactLayerTwo : ℝ) < (invLayer (2 * invGamma) : ℝ) := by
    exact_mod_cast invLayer_majorant_Two
  have hthird : (1 / 3 : ℝ) = ((1 / 3 : ℚ) : ℝ) := by norm_num
  have hninth : (1 / 9 : ℝ) = ((1 / 9 : ℚ) : ℝ) := by norm_num
  calc
    rootLayerSum (2 * γ) =
        8 * localizationProfileT (1 / 3) z -
          32 * localizationProfileT (1 / 9) z + z ^ 2 := hLayer
    _ ≤ 8 * localizationProfileT (1 / 3) z₀ -
          32 * localizationProfileT (1 / 9) z₀ + z₀ ^ 2 := hprofile
    _ = (invExactLayerTwo : ℝ) := by
      rw [hthird, hninth]
      exact_mod_cast hprofile₀
    _ ≤ (invLayer (2 * invGamma) : ℝ) := hnum.le

/-- The first-local source coefficient is dominated by the certified
numeric profile throughout the molecular gamma range. -/
theorem bank_first_root_Li_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17 / 50000) :
    rootLi γ .firstLocal ≤ (invFirstLi : ℝ) := by
  have hLayer := bank_root_layer_sum_endpoint γ hγ hγ₀
  have hmean : rootMeanCap .firstLocal = 29 / 25 := rfl
  have hcoef : 3 * (planarGradientCharge 40 + 1) = (invFirstC : ℝ) := by
    norm_num [planarGradientCharge, invFirstC]
  have hMoment : densityMomentBudget (rootQ .firstLocal) 2 600 =
      (invInverseM2 : ℝ) := by
    rw [show rootQ .firstLocal = (invInverseQ : ℝ) by rfl,
      densityMomentBudget]
    exact inverse_moment_polynomials.1
  have hτ : rootTau .firstLocal = 10000000000 := by
    norm_num [rootTau]
  have hEnvelope : rootResponseEnvelope (6 * rootTau .firstLocal) ≤
      12 * rootTau .firstLocal + 2 := by
    rw [hτ]
    have ht : 0 ≤ (6 : ℝ) * 10000000000 := by positivity
    have hsqrt : Real.sqrt ((6 * (10000000000 : ℝ)) *
        (6 * (10000000000 : ℝ) + 2)) ≤ 6 * (10000000000 : ℝ) + 1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith
    unfold rootResponseEnvelope
    nlinarith
  have hEnvelope0 : 0 ≤ rootResponseEnvelope (6 * rootTau .firstLocal) := by
    rw [show rootTau .firstLocal = 10000000000 by norm_num [rootTau]]
    unfold rootResponseEnvelope
    positivity
  let x : ℚ := (17444 / 10000) * (1 + invInverseTau) *
    (10 / (16000000 * (1 + invInverseTau)))
  have hrootExp : rootEdelta .firstLocal = Real.exp (x : ℝ) := by
    unfold rootEdelta
    rw [show 10 * waveGateEta (rootWaveTuple .firstLocal) =
        (10 * (Numerics.Wave.inverseEta : ℚ) : ℝ) by
          norm_num [rootWaveTuple, waveGateEta]]
    norm_num [rootTau, rootWaveTuple, waveGateEta,
      Numerics.Wave.inverseEta, Numerics.Wave.inverseTau, invInverseTau, x]
  have hExp : rootEdelta .firstLocal ≤ (invFirstEd : ℝ) := by
    have hx0 : 0 ≤ (x : ℝ) := by norm_num [x, invInverseTau]
    have hx1 : (x : ℝ) < 1 := by norm_num [x, invInverseTau]
    have hb := Real.exp_bound_div_one_sub_of_interval hx0 hx1
    have hinv : (invFirstEd : ℝ) = 1 / (1 - (x : ℝ)) := by
      norm_num [invFirstEd, invE, invInverseTau, x]
    rw [hrootExp, hinv]
    exact hb
  have hM2 : 0 ≤ (invInverseM2 : ℝ) := by
    norm_num [invInverseM2]
  have hC : 0 ≤ (invFirstC : ℝ) := by
    norm_num [invFirstC]
  have hInner :
      rootMeanCap .firstLocal +
        3 * (planarGradientCharge 40 + 1) *
          rootResponseEnvelope (6 * rootTau .firstLocal) *
          densityMomentBudget (rootQ .firstLocal) 2 600 ≤
        (29 / 25 : ℝ) + (invFirstC : ℝ) *
          (12 * invInverseTau + 2) * (invInverseM2 : ℝ) := by
    rw [hmean, hcoef, hMoment]
    calc
      29 / 25 + (invFirstC : ℝ) *
          rootResponseEnvelope (6 * rootTau .firstLocal) *
          (invInverseM2 : ℝ) ≤
        29 / 25 + (invFirstC : ℝ) *
          (12 * rootTau .firstLocal + 2) * (invInverseM2 : ℝ) := by
            have hmul := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hEnvelope hC) hM2
            nlinarith [hmul]
      _ = (29 / 25 : ℝ) + (invFirstC : ℝ) *
          (12 * invInverseTau + 2) * (invInverseM2 : ℝ) := by
            rw [hτ]
            norm_num [invInverseTau]
  have hInner0 : 0 ≤ (29 / 25 : ℝ) + (invFirstC : ℝ) *
      (12 * invInverseTau + 2) * (invInverseM2 : ℝ) := by
    exact add_nonneg (by norm_num) (mul_nonneg
      (mul_nonneg hC (by norm_num [invInverseTau])) hM2)
  have hActual0 : 0 ≤ rootMeanCap .firstLocal +
      3 * (planarGradientCharge 40 + 1) *
        rootResponseEnvelope (6 * rootTau .firstLocal) *
        densityMomentBudget (rootQ .firstLocal) 2 600 := by
    rw [hmean, hcoef, hMoment]
    exact add_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg hC hEnvelope0) hM2)
  have hEd0 : 0 ≤ (invFirstEd : ℝ) := by
    norm_num [invFirstEd, invE, invInverseTau]
  have hLayer0 : 0 ≤ rootLayerSum (2 * γ) := by
    unfold rootLayerSum
    apply tsum_nonneg
    intro n
    exact mul_nonneg (bankLayerWeight_nonneg n) (by positivity)
  have hNumEq : (invFirstLi : ℝ) = (invFirstEd : ℝ) *
      ((29 / 25 : ℝ) + (invFirstC : ℝ) *
        (12 * invInverseTau + 2) * (invInverseM2 : ℝ)) *
      (invLayer (2 * invGamma) : ℝ) := by
    norm_num [invFirstLi]
  change rootEdelta .firstLocal *
      (rootMeanCap .firstLocal +
        3 * (planarGradientCharge 40 + 1) *
          rootResponseEnvelope (6 * rootTau .firstLocal) *
          densityMomentBudget (rootQ .firstLocal) 2 600) *
      rootLayerSum (2 * γ) ≤ (invFirstLi : ℝ)
  rw [hNumEq]
  calc
    rootEdelta .firstLocal *
        (rootMeanCap .firstLocal +
          3 * (planarGradientCharge 40 + 1) *
            rootResponseEnvelope (6 * rootTau .firstLocal) *
            densityMomentBudget (rootQ .firstLocal) 2 600) *
        rootLayerSum (2 * γ) ≤
      (invFirstEd : ℝ) *
        ((29 / 25 : ℝ) + (invFirstC : ℝ) *
          (12 * invInverseTau + 2) * (invInverseM2 : ℝ)) *
        rootLayerSum (2 * γ) := by
          calc
            rootEdelta .firstLocal *
                (rootMeanCap .firstLocal +
                  3 * (planarGradientCharge 40 + 1) *
                    rootResponseEnvelope (6 * rootTau .firstLocal) *
                    densityMomentBudget (rootQ .firstLocal) 2 600) *
                rootLayerSum (2 * γ) ≤
              (invFirstEd : ℝ) *
                (rootMeanCap .firstLocal +
                  3 * (planarGradientCharge 40 + 1) *
                    rootResponseEnvelope (6 * rootTau .firstLocal) *
                    densityMomentBudget (rootQ .firstLocal) 2 600) *
                rootLayerSum (2 * γ) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hExp hActual0) hLayer0
            _ ≤ (invFirstEd : ℝ) *
                ((29 / 25 : ℝ) + (invFirstC : ℝ) *
                  (12 * invInverseTau + 2) * (invInverseM2 : ℝ)) *
                rootLayerSum (2 * γ) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hInner hEd0) hLayer0
    _ ≤ (invFirstEd : ℝ) *
        ((29 / 25 : ℝ) + (invFirstC : ℝ) *
          (12 * invInverseTau + 2) * (invInverseM2 : ℝ)) *
        (invLayer (2 * invGamma) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hLayer
            (mul_nonneg hEd0 hInner0)

private theorem bank_root_response_envelope_linear (t : ℝ) (ht : 0 ≤ t) :
    rootResponseEnvelope t ≤ 2 * t + 2 := by
  have hsqrt : Real.sqrt (t * (t + 2)) ≤ t + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (t + 1)]
  unfold rootResponseEnvelope
  linarith

private theorem bank_root_error_budgets_bound
    (γ : ℝ) (r : RootRow) (Ed M0 Z0 C Menv Denv : ℝ)
    (hEd : rootEdelta r ≤ Ed)
    (hMatrix : (∑' hk : ℕ × ℕ,
      Real.sqrt (bankLayerWeight hk.2) *
        (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
        (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) ≤ M0)
    (hDensity : densityResetPowerSum (2*γ) (1/2) (rootH0 r-38) ≤ Z0)
    (hDensity0 : 0 ≤ densityResetPowerSum (2*γ) (1/2) (rootH0 r-38))
    (hC : 3 * (planarGradientCharge 40 + 1) = C)
    (hMenv : rootResponseEnvelope (rootTau r) ≤ Menv)
    (hDenv : rootResponseEnvelope (6*rootTau r) ≤ Denv)
    (hEd0 : 0 ≤ Ed) (hC0 : 0 ≤ C) (hMenv0 : 0 ≤ Menv) :
    rootMatrixErrorBudget γ 256 r + rootDensityErrorBudget γ r ≤
      Ed * (4096 * Menv * M0 + 3 * C * Denv * Z0) := by
  have hmatrix : rootMatrixErrorBudget γ 256 r ≤ Ed * 4096 * Menv * M0 := by
    unfold rootMatrixErrorBudget
    rw [show Real.sqrt (256:ℝ) = 16 by
      calc
        _ = Real.sqrt ((16:ℝ)^2) := by norm_num
        _ = |(16:ℝ)| := Real.sqrt_sq_eq_abs _
        _ = 16 := by norm_num]
    have hTau0 : 0 ≤ rootTau r := by
      cases r <;> norm_num [rootTau]
    have hResp0 : 0 ≤ rootResponseEnvelope (rootTau r) := by
      unfold rootResponseEnvelope
      positivity
    have hseries0 : 0 ≤ (∑' hk : ℕ × ℕ,
        Real.sqrt (bankLayerWeight hk.2) *
          (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
          (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) := by
      apply tsum_nonneg
      intro hk
      positivity
    calc
      _ = rootEdelta r *
          (256 * 16 * rootResponseEnvelope (rootTau r) *
            (∑' hk : ℕ × ℕ,
              Real.sqrt (bankLayerWeight hk.2) *
                (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
                (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1)))) := by ring
      _ ≤ Ed *
          (256 * 16 * rootResponseEnvelope (rootTau r) *
            (∑' hk : ℕ × ℕ,
              Real.sqrt (bankLayerWeight hk.2) *
                (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
                (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1)))) :=
          mul_le_mul_of_nonneg_right hEd (by positivity)
      _ = Ed * 256 * 16 * rootResponseEnvelope (rootTau r) *
          (∑' hk : ℕ × ℕ,
            Real.sqrt (bankLayerWeight hk.2) *
              (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
              (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) := by ring
      _ = (Ed * 4096) * rootResponseEnvelope (rootTau r) *
          (∑' hk : ℕ × ℕ,
            Real.sqrt (bankLayerWeight hk.2) *
              (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
              (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) := by ring
      _ ≤ (Ed * 4096) * Menv *
          (∑' hk : ℕ × ℕ,
            Real.sqrt (bankLayerWeight hk.2) *
              (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
              (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMenv (mul_nonneg hEd0 (by norm_num))) hseries0
      _ ≤ (Ed * 4096) * Menv * M0 := by
        exact mul_le_mul_of_nonneg_left hMatrix (mul_nonneg (mul_nonneg hEd0 (by norm_num)) hMenv0)
      _ = Ed * 4096 * Menv * M0 := by ring
  have hEZ : densityEZ γ (planarGradientCharge 40) (rootH0 r-38) ≤
      3 * C * Z0 := by
    unfold densityEZ
    have hsqrt3 : (3:ℝ)^(1/2:ℝ) ≤ 2 := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_iff.mpr
      constructor <;> norm_num
    have hpow : (3:ℝ)^(2*(1/2:ℝ)) = 3 := by
      rw [show (2*(1/2:ℝ)) = 1 by norm_num, Real.rpow_one]
    have hS : 0 ≤ planarGradientCharge 40 + 1 := by
      norm_num [planarGradientCharge]
    have hfactor :
        1 + (3:ℝ)^(1/2:ℝ) + (3:ℝ)^(2*(1/2:ℝ)) ≤ 9 := by
      rw [hpow]
      linarith only [hsqrt3]
    have hscale :
        (planarGradientCharge 40 + 1) *
            (1 + (3:ℝ)^(1/2:ℝ) + (3:ℝ)^(2*(1/2:ℝ))) ≤
          3 * C := by
      calc
        _ ≤ (planarGradientCharge 40 + 1) * 9 :=
          mul_le_mul_of_nonneg_left hfactor hS
        _ = 3 * C := by rw [← hC]; ring
    calc
      _ ≤ 3 * C * densityResetPowerSum (2*γ) (1/2) (rootH0 r-38) :=
        mul_le_mul_of_nonneg_right hscale hDensity0
      _ ≤ 3 * C * Z0 := mul_le_mul_of_nonneg_left hDensity (by positivity)
  have hdenv0 : 0 ≤ rootResponseEnvelope (6*rootTau r) := by
    have htau0 : 0 ≤ rootTau r := by
      cases r <;> norm_num [rootTau]
    unfold rootResponseEnvelope
    positivity
  have hEZ0 : 0 ≤ densityEZ γ (planarGradientCharge 40) (rootH0 r-38) := by
    unfold densityEZ
    exact mul_nonneg
      (mul_nonneg (by norm_num [planarGradientCharge]) (by positivity)) hDensity0
  have hZ00 : 0 ≤ Z0 := le_trans hDensity0 hDensity
  have hdensity : rootDensityErrorBudget γ r ≤ Ed * (3*C*Denv*Z0) := by
    unfold rootDensityErrorBudget
    calc
      _ ≤ Ed * rootResponseEnvelope (6*rootTau r) *
          densityEZ γ (planarGradientCharge 40) (rootH0 r-38) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hEd hdenv0) hEZ0
      _ ≤ Ed * rootResponseEnvelope (6*rootTau r) * (3*C*Z0) :=
        mul_le_mul_of_nonneg_left hEZ (mul_nonneg hEd0 hdenv0)
      _ ≤ Ed * Denv * (3*C*Z0) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDenv hEd0)
          (mul_nonneg (mul_nonneg (by norm_num) hC0) hZ00)
      _ = Ed * (3*C*Denv*Z0) := by ring
  calc
    _ ≤ Ed * (4096*Menv*M0) + Ed * (3*C*Denv*Z0) := by
      exact add_le_add (by simpa [mul_assoc] using hmatrix)
        (by simpa [mul_assoc] using hdensity)
    _ = Ed * (4096*Menv*M0 + 3*C*Denv*Z0) := by ring

private theorem bank_root_error_profile_bound
    (γ : ℝ) (r : RootRow) (Ed M0 Z0 C τ : ℝ) (NM NZ Cdepth : ℕ)
    (hγ : 0 ≤ γ) (hγ₀ : γ ≤ 17/50000)
    (hdepth : rootH0 r-38 = Cdepth) (hTau : rootTau r = τ)
    (hNM : (NM:ℝ) ≤ (99/100)*((Cdepth+1:ℕ):ℝ))
    (hNZ : (NZ:ℝ) ≤ (49/100)*((Cdepth+1:ℕ):ℝ))
    (hEd : rootEdelta r ≤ Ed)
    (hM0 : M0 = (2/3:ℝ)*(3:ℝ)^(-(NM:ℝ))/(66/100)^2)
    (hZ0 : Z0 = (3:ℝ)^(-(NZ:ℝ))/(41/100)^2)
    (hC : 3*(planarGradientCharge 40+1) = C) :
    rootMatrixErrorBudget γ 256 r + rootDensityErrorBudget γ r ≤
      Ed * (4096*(2*τ+2)*M0 + 3*C*(12*τ+2)*Z0) := by
  have hmatrix0 := bank_root_matrix_series_bound γ hγ hγ₀ Cdepth NM hNM
  rw [← hdepth, ← hM0] at hmatrix0
  have hdensity0 := bank_root_density_series_bound γ hγ hγ₀ Cdepth NZ hNZ
  rw [← hdepth, ← hZ0] at hdensity0
  have hpower0 := bank_root_density_power_nonneg γ hγ₀ Cdepth
  rw [← hdepth] at hpower0
  have htau0 : 0 ≤ τ := by
    rw [← hTau]
    cases r <;> norm_num [rootTau]
  have hEd0 : 0 ≤ Ed := (Real.exp_nonneg _).trans hEd
  have hC0 : 0 ≤ C := by rw [← hC]; norm_num [planarGradientCharge]
  have hMenv : rootResponseEnvelope (rootTau r) ≤ 2*τ+2 := by
    rw [hTau]
    exact bank_root_response_envelope_linear τ htau0
  have hDenv : rootResponseEnvelope (6*rootTau r) ≤ 12*τ+2 := by
    rw [hTau]
    have h := bank_root_response_envelope_linear (6*τ) (by positivity)
    nlinarith only [h]
  have hMenv0 : 0 ≤ 2*τ+2 := by positivity
  exact bank_root_error_budgets_bound γ r Ed M0 Z0 C (2*τ+2) (12*τ+2)
    hEd hmatrix0 hdensity0 hpower0 hC hMenv hDenv hEd0 hC0 hMenv0

private theorem bank_root_Li_bound_of_majorants
    (γ : ℝ) (r : RootRow) (Ed mean C U moment layer : ℝ)
    (hEd : rootEdelta r ≤ Ed)
    (hMean : rootMeanCap r = mean)
    (hC : 3 * (planarGradientCharge 40 + 1) = C)
    (hEnvelope : rootResponseEnvelope (6 * rootTau r) ≤ U)
    (hMoment : densityMomentBudget (rootQ r) 2 (rootMomentCutoff r) = moment)
    (hLayer : rootLayerSum (2 * γ) ≤ layer)
    (hTau0 : 0 ≤ rootTau r)
    (hEd0 : 0 ≤ Ed) (hMean0 : 0 ≤ mean) (hC0 : 0 ≤ C)
    (hU0 : 0 ≤ U) (hMoment0 : 0 ≤ moment) :
    rootLi γ r ≤ Ed * (mean + C * U * moment) * layer := by
  change rootEdelta r * (rootMeanCap r +
      3 * (planarGradientCharge 40 + 1) *
        rootResponseEnvelope (6 * rootTau r) *
        densityMomentBudget (rootQ r) 2 (rootMomentCutoff r)) *
      rootLayerSum (2 * γ) ≤ _
  rw [hMean, hC, hMoment]
  have hInner : mean + C * rootResponseEnvelope (6 * rootTau r) * moment ≤
      mean + C * U * moment := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEnvelope hC0) hMoment0
    linarith
  have hInner0 : 0 ≤ mean + C * rootResponseEnvelope (6 * rootTau r) * moment :=
    add_nonneg hMean0 (mul_nonneg
      (mul_nonneg hC0 (by
        have ht : 0 ≤ 6 * rootTau r := by positivity
        unfold rootResponseEnvelope
        positivity)) hMoment0)
  have hTargetInner0 : 0 ≤ mean + C * U * moment :=
    add_nonneg hMean0 (mul_nonneg (mul_nonneg hC0 hU0) hMoment0)
  have hSeries0 : 0 ≤ rootLayerSum (2 * γ) := by
    unfold rootLayerSum
    apply tsum_nonneg
    intro n
    exact mul_nonneg (bankLayerWeight_nonneg n) (by positivity)
  calc
    _ ≤ Ed * (mean + C * rootResponseEnvelope (6 * rootTau r) * moment) *
        rootLayerSum (2 * γ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hEd hInner0) hSeries0
    _ ≤ Ed * (mean + C * U * moment) * rootLayerSum (2 * γ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hInner hEd0)
        hSeries0
    _ ≤ Ed * (mean + C * U * moment) * layer := by
      exact mul_le_mul_of_nonneg_left hLayer
        (mul_nonneg hEd0 hTargetInner0)

private theorem bank_inverse_root_Edelta_bound (r : RootRow) (hr : r ≠ .full) :
    rootEdelta r ≤ (invFirstEd : ℝ) := by
  have hrow : rootEdelta r = rootEdelta .firstLocal := by
    cases r with
    | globalInverse => rfl
    | localInverse => rfl
    | firstLocal => rfl
    | full => exact False.elim (hr rfl)
  rw [hrow]
  let x : ℚ := (17444 / 10000) * (1 + invInverseTau) *
    (10 / (16000000 * (1 + invInverseTau)))
  have hrootExp : rootEdelta .firstLocal = Real.exp (x : ℝ) := by
    unfold rootEdelta
    rw [show 10 * waveGateEta (rootWaveTuple .firstLocal) =
        (10 * (Numerics.Wave.inverseEta : ℚ) : ℝ) by
          norm_num [rootWaveTuple, waveGateEta]]
    norm_num [rootTau, rootWaveTuple, waveGateEta,
      Numerics.Wave.inverseEta, Numerics.Wave.inverseTau, invInverseTau, x]
  have hx0 : 0 ≤ (x : ℝ) := by norm_num [x, invInverseTau]
  have hx1 : (x : ℝ) < 1 := by norm_num [x, invInverseTau]
  have hb := Real.exp_bound_div_one_sub_of_interval hx0 hx1
  have hinv : (invFirstEd : ℝ) = 1 / (1 - (x : ℝ)) := by
    norm_num [invFirstEd, invE, invInverseTau, x]
  rw [hrootExp, hinv]
  exact hb

private theorem bank_full_root_Edelta_bound :
    rootEdelta .full ≤ (invFullEd : ℝ) := by
  let x : ℚ := (17444 / 10000) * (1 + invFullTau) *
    (10 / (80 * (1 + invFullTau)))
  have hrootExp : rootEdelta .full = Real.exp (x : ℝ) := by
    unfold rootEdelta
    rw [show 10 * waveGateEta (rootWaveTuple .full) =
        (10 * (Numerics.Wave.fullEta : ℚ) : ℝ) by
          norm_num [rootWaveTuple, waveGateEta]]
    norm_num [rootTau, rootWaveTuple, waveGateEta,
      Numerics.Wave.fullEta, Numerics.Wave.fullTau, invFullTau, x]
  have hx0 : 0 ≤ (x : ℝ) := by norm_num [x, invFullTau]
  have hx1 : (x : ℝ) < 1 := by norm_num [x, invFullTau]
  have hb := Real.exp_bound_div_one_sub_of_interval hx0 hx1
  have hinv : (invFullEd : ℝ) = 1 / (1 - (x : ℝ)) := by
    norm_num [invFullEd, invE, invFullTau, x]
  rw [hrootExp, hinv]
  exact hb

theorem bank_first_root_error_budget_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootMatrixErrorBudget γ 256 .firstLocal + rootDensityErrorBudget γ .firstLocal ≤
      (invFirstEd:ℝ) *
        (4096*(2*(invInverseTau:ℝ)+2)*(invFirstM0:ℝ)+
          3*(invFirstC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invFirstZ0:ℝ)) := by
  have hEd := bank_inverse_root_Edelta_bound .firstLocal (by decide)
  have hC : 3*(planarGradientCharge 40+1) = (invFirstC:ℝ) := by
    norm_num [planarGradientCharge, invFirstC]
  have hM0 : (invFirstM0:ℝ) =
      (2/3:ℝ)*(3:ℝ)^(-(336:ℝ))/(66/100)^2 := by norm_num [invFirstM0]
  have hZ0 : (invFirstZ0:ℝ) =
      (3:ℝ)^(-(166:ℝ))/(41/100)^2 := by norm_num [invFirstZ0]
  have hcore := bank_root_error_profile_bound γ .firstLocal
    (invFirstEd:ℝ) (invFirstM0:ℝ) (invFirstZ0:ℝ) (invFirstC:ℝ)
    (invInverseTau:ℝ) 336 166 339 hγ hγ₀
    (by norm_num [rootH0]) (by norm_num [rootTau, invInverseTau])
    (by norm_num) (by norm_num) hEd hM0 hZ0 hC
  exact hcore

theorem bank_global_root_error_budget_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootMatrixErrorBudget γ 256 .globalInverse +
      rootDensityErrorBudget γ .globalInverse ≤
      (invGlobalEd:ℝ) *
        (4096*(2*(invInverseTau:ℝ)+2)*(invGlobalM0:ℝ)+
          3*(invGlobalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invGlobalZ0:ℝ)) := by
  have hEd := bank_inverse_root_Edelta_bound .globalInverse (by decide)
  have hC : 3*(planarGradientCharge 40+1) = (invGlobalC:ℝ) := by
    norm_num [planarGradientCharge, invGlobalC]
  have hM0 : (invGlobalM0:ℝ) =
      (2/3:ℝ)*(3:ℝ)^(-(293:ℝ))/(66/100)^2 := by norm_num [invGlobalM0]
  have hZ0 : (invGlobalZ0:ℝ) =
      (3:ℝ)^(-(145:ℝ))/(41/100)^2 := by norm_num [invGlobalZ0]
  have hcore := bank_root_error_profile_bound γ .globalInverse
    (invGlobalEd:ℝ) (invGlobalM0:ℝ) (invGlobalZ0:ℝ) (invGlobalC:ℝ)
    (invInverseTau:ℝ) 293 145 295 hγ hγ₀
    (by norm_num [rootH0]) (by norm_num [rootTau, invInverseTau])
    (by norm_num) (by norm_num) hEd hM0 hZ0 hC
  exact hcore

theorem bank_local_root_error_budget_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootMatrixErrorBudget γ 256 .localInverse +
      rootDensityErrorBudget γ .localInverse ≤
      (invLocalEd:ℝ) *
        (4096*(2*(invInverseTau:ℝ)+2)*(invLocalM0:ℝ)+
          3*(invLocalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invLocalZ0:ℝ)) := by
  have hEd := bank_inverse_root_Edelta_bound .localInverse (by decide)
  have hC : 3*(planarGradientCharge 40+1) = (invLocalC:ℝ) := by
    norm_num [planarGradientCharge, invLocalC]
  have hM0 : (invLocalM0:ℝ) =
      (2/3:ℝ)*(3:ℝ)^(-(336:ℝ))/(66/100)^2 := by norm_num [invLocalM0]
  have hZ0 : (invLocalZ0:ℝ) =
      (3:ℝ)^(-(166:ℝ))/(41/100)^2 := by norm_num [invLocalZ0]
  have hcore := bank_root_error_profile_bound γ .localInverse
    (invLocalEd:ℝ) (invLocalM0:ℝ) (invLocalZ0:ℝ) (invLocalC:ℝ)
    (invInverseTau:ℝ) 336 166 339 hγ hγ₀
    (by norm_num [rootH0]) (by norm_num [rootTau, invInverseTau])
    (by norm_num) (by norm_num) hEd hM0 hZ0 hC
  exact hcore

theorem bank_full_root_error_budget_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootMatrixErrorBudget γ 256 .full + rootDensityErrorBudget γ .full ≤
      (invFullEd:ℝ) *
        (4096*(2*(invFullTau:ℝ)+2)*((2/3:ℚ)*(1/3^336)/(66/100)^2:ℝ)+
          3*(invFullC:ℝ)*(12*(invFullTau:ℝ)+2)*((1/3^166)/(41/100)^2:ℝ)) := by
  have hEd := bank_full_root_Edelta_bound
  have hC : 3*(planarGradientCharge 40+1) = (invFullC:ℝ) := by
    norm_num [planarGradientCharge, invFullC]
  have hM0 : ((2/3:ℚ)*(1/3^336)/(66/100)^2:ℝ) =
      (2/3:ℝ)*(3:ℝ)^(-(336:ℝ))/(66/100)^2 := by norm_num
  have hZ0 : ((1/3^166)/(41/100)^2:ℝ) =
      (3:ℝ)^(-(166:ℝ))/(41/100)^2 := by norm_num
  have hcore := bank_root_error_profile_bound γ .full
    (invFullEd:ℝ) ((2/3:ℚ)*(1/3^336)/(66/100)^2:ℝ)
    ((1/3^166)/(41/100)^2:ℝ) (invFullC:ℝ) (invFullTau:ℝ)
    336 166 339 hγ hγ₀ (by norm_num [rootH0])
    (by norm_num [rootTau, invFullTau]) (by norm_num) (by norm_num)
    hEd hM0 hZ0 hC
  exact hcore

theorem bank_global_root_Li_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17 / 50000) :
    rootLi γ .globalInverse ≤ (invGlobalLi : ℝ) := by
  have hEd := bank_inverse_root_Edelta_bound .globalInverse (by decide)
  have hLayer := bank_root_layer_sum_endpoint γ hγ hγ₀
  have hMean : rootMeanCap .globalInverse = 10747 / 10000 := rfl
  have hC : 3 * (planarGradientCharge 40 + 1) = (invGlobalC : ℝ) := by
    norm_num [planarGradientCharge, invGlobalC]
  have hTau : rootTau .globalInverse = 10000000000 := by norm_num [rootTau]
  have hEnvelope : rootResponseEnvelope (6 * rootTau .globalInverse) ≤
      12 * (invInverseTau : ℝ) + 2 := by
    rw [hTau]
    have ht : 0 ≤ (6 : ℝ) * 10000000000 := by positivity
    have h := bank_root_response_envelope_linear (6 * (10000000000 : ℝ)) ht
    norm_num [invInverseTau] at h ⊢
    exact h
  have hMoment : densityMomentBudget (rootQ .globalInverse) 2 600 =
      (invInverseM2 : ℝ) := by
    rw [show rootQ .globalInverse = (invInverseQ : ℝ) by rfl,
      densityMomentBudget]
    exact inverse_moment_polynomials.1
  have hEd0 : 0 ≤ (invGlobalEd : ℝ) := by
    norm_num [invGlobalEd, invE, invInverseTau]
  have hC0 : 0 ≤ (invGlobalC : ℝ) := by norm_num [invGlobalC]
  have hMoment0 : 0 ≤ (invInverseM2 : ℝ) := by norm_num [invInverseM2]
  have hcore := bank_root_Li_bound_of_majorants γ .globalInverse
    (invGlobalEd : ℝ) (10747 / 10000) (invGlobalC : ℝ)
    (12 * (invInverseTau : ℝ) + 2) (invInverseM2 : ℝ)
    (invLayer (2 * invGamma) : ℝ) (hEd.trans_eq (by rfl) ) hMean hC hEnvelope
    hMoment hLayer (by norm_num [rootTau]) hEd0 (by norm_num) hC0
    (by norm_num [invInverseTau]) hMoment0
  have hprofile : (invGlobalLi : ℝ) = (invGlobalEd : ℝ) *
      (10747 / 10000 + (invGlobalC : ℝ) *
        (12 * (invInverseTau : ℝ) + 2) * (invInverseM2 : ℝ)) *
      (invLayer (2 * invGamma) : ℝ) := by
    norm_num [invGlobalLi, invGlobalEd]
  simpa only [hprofile] using hcore

theorem bank_local_root_Li_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17 / 50000) :
    rootLi γ .localInverse ≤ (invLocalLi : ℝ) := by
  have hroot : rootLi γ .localInverse = rootLi γ .globalInverse := rfl
  have hprofile : (invGlobalLi : ℝ) = (invLocalLi : ℝ) := by rfl
  rw [hroot, ← hprofile]
  exact bank_global_root_Li_bound γ hγ hγ₀

theorem bank_full_root_Li_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17 / 50000) :
    rootLi γ .full ≤ (invFullLi : ℝ) := by
  have hEd := bank_full_root_Edelta_bound
  have hLayer := bank_root_layer_sum_endpoint γ hγ hγ₀
  have hMean : rootMeanCap .full = 29 / 25 := rfl
  have hC : 3 * (planarGradientCharge 40 + 1) = (invFullC : ℝ) := by
    norm_num [planarGradientCharge, invFullC]
  have hTau : rootTau .full = 5000000000000000 := by norm_num [rootTau]
  have hEnvelope : rootResponseEnvelope (6 * rootTau .full) ≤
      12 * (invFullTau : ℝ) + 2 := by
    rw [hTau]
    have ht : 0 ≤ (6 : ℝ) * 5000000000000000 := by positivity
    have h := bank_root_response_envelope_linear (6 * (5000000000000000 : ℝ)) ht
    norm_num [invFullTau] at h ⊢
    exact h
  have hMoment : densityMomentBudget (rootQ .full) 2 1232 =
      (invFullM2 : ℝ) := by
    rw [show rootQ .full = (invFullQ : ℝ) by rfl,
      densityMomentBudget]
    exact full_moment_polynomials.1
  have hEd0 : 0 ≤ (invFullEd : ℝ) := by
    norm_num [invFullEd, invE, invFullTau]
  have hC0 : 0 ≤ (invFullC : ℝ) := by norm_num [invFullC]
  have hMoment0 : 0 ≤ (invFullM2 : ℝ) := by norm_num [invFullM2]
  have hcore := bank_root_Li_bound_of_majorants γ .full
    (invFullEd : ℝ) (29 / 25) (invFullC : ℝ)
    (12 * (invFullTau : ℝ) + 2) (invFullM2 : ℝ)
    (invLayer (2 * invGamma) : ℝ) hEd hMean hC hEnvelope hMoment hLayer
    (by norm_num [rootTau]) hEd0 (by norm_num) hC0 (by norm_num [invFullTau])
    hMoment0
  have hprofile : (invFullLi : ℝ) = (invFullEd : ℝ) *
      (29 / 25 + (invFullC : ℝ) *
        (12 * (invFullTau : ℝ) + 2) * (invFullM2 : ℝ)) *
      (invLayer (2 * invGamma) : ℝ) := by
    norm_num [invFullLi, invFullEd]
  simpa only [hprofile] using hcore

theorem bank_first_root_Li_lt_two (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) : rootLi γ .firstLocal < 2 := by
  have hLi := bank_first_root_Li_bound γ hγ hγ₀
  have hnum : (invFirstLi:ℝ) < 2 := by
    norm_num [invFirstLi, invFirstEd, invFirstC, invInverseM2,
      invInverseTau, invLayer, invE, invGamma]
  exact hLi.trans_lt hnum

theorem bank_global_root_Li_lt_two (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) : rootLi γ .globalInverse < 2 := by
  have hLi := bank_global_root_Li_bound γ hγ hγ₀
  have hnum : (invGlobalLi:ℝ) < 2 := by
    norm_num [invGlobalLi, invGlobalEd, invGlobalC, invInverseM2,
      invInverseTau, invLayer, invE, invGamma]
  exact hLi.trans_lt hnum

theorem bank_local_root_Li_lt_two (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) : rootLi γ .localInverse < 2 := by
  have hLi := bank_local_root_Li_bound γ hγ hγ₀
  have hnum : (invLocalLi:ℝ) < 2 := by
    norm_num [invLocalLi, invLocalEd, invLocalC, invInverseM2,
      invInverseTau, invLayer, invE, invGamma]
  exact hLi.trans_lt hnum

theorem bank_full_root_Li_lt_two (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) : rootLi γ .full < 2 := by
  have hLi := bank_full_root_Li_bound γ hγ hγ₀
  have hnum : (invFullLi:ℝ) < 2 := by
    norm_num [invFullLi, invFullEd, invFullC, invFullM2, invFullTau,
      invInverseM2, invInverseTau, invLayer, invE, invGamma]
  exact hLi.trans_lt hnum

theorem bank_first_root_error_plus_tiny_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootLi γ .firstLocal * selectedRootTiny (rootH0 .firstLocal) +
      (rootMatrixErrorBudget γ 256 .firstLocal +
        rootDensityErrorBudget γ .firstLocal) ≤ (invFirstRho:ℝ) := by
  have hbudget := bank_first_root_error_budget_bound γ hγ hγ₀
  have hLi := bank_first_root_Li_lt_two γ hγ hγ₀
  have htiny : selectedRootTiny (rootH0 .firstLocal) = 1/10^40 := by
    norm_num [rootH0, selectedRootTiny]
  rw [htiny]
  have hRho : (invFirstEd:ℝ) *
      (4096*(2*(invInverseTau:ℝ)+2)*(invFirstM0:ℝ)+
        3*(invFirstC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invFirstZ0:ℝ)) +
      2*(1/10^40:ℝ) = (invFirstRho:ℝ) := by norm_num [invFirstRho]
  calc
    _ ≤ 2*(1/10^40:ℝ) +
        ((invFirstEd:ℝ) *
          (4096*(2*(invInverseTau:ℝ)+2)*(invFirstM0:ℝ)+
            3*(invFirstC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invFirstZ0:ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hLi.le (by positivity)) hbudget
    _ = (invFirstEd:ℝ) *
        (4096*(2*(invInverseTau:ℝ)+2)*(invFirstM0:ℝ)+
          3*(invFirstC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invFirstZ0:ℝ)) +
          2*(1/10^40:ℝ) := by rw [add_comm]
    _ = (invFirstRho:ℝ) := hRho

theorem bank_global_root_error_plus_tiny_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootLi γ .globalInverse * selectedRootTiny (rootH0 .globalInverse) +
      (rootMatrixErrorBudget γ 256 .globalInverse +
        rootDensityErrorBudget γ .globalInverse) ≤ (invGlobalRho:ℝ) := by
  have hbudget := bank_global_root_error_budget_bound γ hγ hγ₀
  have hLi := bank_global_root_Li_lt_two γ hγ hγ₀
  have htiny : selectedRootTiny (rootH0 .globalInverse) = 1/10^30 := by
    norm_num [rootH0, selectedRootTiny]
  rw [htiny]
  have hRho : (invGlobalEd:ℝ) *
      (4096*(2*(invInverseTau:ℝ)+2)*(invGlobalM0:ℝ)+
        3*(invGlobalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invGlobalZ0:ℝ)) +
      2*(1/10^30:ℝ) = (invGlobalRho:ℝ) := by norm_num [invGlobalRho]
  calc
    _ ≤ 2*(1/10^30:ℝ) +
        ((invGlobalEd:ℝ) *
          (4096*(2*(invInverseTau:ℝ)+2)*(invGlobalM0:ℝ)+
            3*(invGlobalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invGlobalZ0:ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hLi.le (by positivity)) hbudget
    _ = (invGlobalEd:ℝ) *
        (4096*(2*(invInverseTau:ℝ)+2)*(invGlobalM0:ℝ)+
          3*(invGlobalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invGlobalZ0:ℝ)) +
          2*(1/10^30:ℝ) := by rw [add_comm]
    _ = (invGlobalRho:ℝ) := hRho

theorem bank_local_root_error_plus_tiny_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootLi γ .localInverse * selectedRootTiny (rootH0 .localInverse) +
      (rootMatrixErrorBudget γ 256 .localInverse +
        rootDensityErrorBudget γ .localInverse) ≤ (invLocalRho:ℝ) := by
  have hbudget := bank_local_root_error_budget_bound γ hγ hγ₀
  have hLi := bank_local_root_Li_lt_two γ hγ hγ₀
  have htiny : selectedRootTiny (rootH0 .localInverse) = 1/10^40 := by
    norm_num [rootH0, selectedRootTiny]
  rw [htiny]
  have hRho : (invLocalEd:ℝ) *
      (4096*(2*(invInverseTau:ℝ)+2)*(invLocalM0:ℝ)+
        3*(invLocalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invLocalZ0:ℝ)) +
      2*(1/10^40:ℝ) = (invLocalRho:ℝ) := by norm_num [invLocalRho]
  calc
    _ ≤ 2*(1/10^40:ℝ) +
        ((invLocalEd:ℝ) *
          (4096*(2*(invInverseTau:ℝ)+2)*(invLocalM0:ℝ)+
            3*(invLocalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invLocalZ0:ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hLi.le (by positivity)) hbudget
    _ = (invLocalEd:ℝ) *
        (4096*(2*(invInverseTau:ℝ)+2)*(invLocalM0:ℝ)+
          3*(invLocalC:ℝ)*(12*(invInverseTau:ℝ)+2)*(invLocalZ0:ℝ)) +
          2*(1/10^40:ℝ) := by rw [add_comm]
    _ = (invLocalRho:ℝ) := hRho

theorem bank_full_root_error_plus_tiny_bound (γ : ℝ) (hγ : 0 ≤ γ)
    (hγ₀ : γ ≤ 17/50000) :
    rootLi γ .full * selectedRootTiny (rootH0 .full) +
      (rootMatrixErrorBudget γ 256 .full + rootDensityErrorBudget γ .full) ≤
        (invFullRho:ℝ) := by
  have hbudget := bank_full_root_error_budget_bound γ hγ hγ₀
  have hLi := bank_full_root_Li_lt_two γ hγ hγ₀
  have htiny : selectedRootTiny (rootH0 .full) = 1/10^40 := by
    norm_num [rootH0, selectedRootTiny]
  rw [htiny]
  have hRho : (invFullEd:ℝ) *
      (4096*(2*(invFullTau:ℝ)+2)*((2/3:ℚ)*(1/3^336)/(66/100)^2:ℝ)+
        3*(invFullC:ℝ)*(12*(invFullTau:ℝ)+2)*((1/3^166)/(41/100)^2:ℝ)) +
      2*(1/10^40:ℝ) = (invFullRho:ℝ) := by
    rw [invFullRho]
    push_cast
    congr 1
    simp only [div_eq_mul_inv, mul_assoc]
    norm_num
  calc
    _ ≤ 2*(1/10^40:ℝ) +
        ((invFullEd:ℝ) *
          (4096*(2*(invFullTau:ℝ)+2)*((2/3:ℚ)*(1/3^336)/(66/100)^2:ℝ)+
            3*(invFullC:ℝ)*(12*(invFullTau:ℝ)+2)*((1/3^166)/(41/100)^2:ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hLi.le (by positivity)) hbudget
    _ = (invFullEd:ℝ) *
        (4096*(2*(invFullTau:ℝ)+2)*((2/3:ℚ)*(1/3^336)/(66/100)^2:ℝ)+
          3*(invFullC:ℝ)*(12*(invFullTau:ℝ)+2)*((1/3^166)/(41/100)^2:ℝ)) +
          2*(1/10^40:ℝ) := by rw [add_comm]
    _ = (invFullRho:ℝ) := hRho

end ASDExplicitGamma.Inverse
