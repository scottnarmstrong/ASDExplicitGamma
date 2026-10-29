module

public import ASDExplicitGamma.Inverse.AssemblyDensityProfile
public import ASDExplicitGamma.Inverse.AssemblyTraceNumerics
public import ASDExplicitGamma.Inverse.FullResponseDecayNumerics

/-! Uniform numerical caps for the two all-height common-noise terms. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
noncomputable section

private theorem corr_linear_le_power (k : ℕ) :
    (k:ℝ) ≤ (3:ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      push_cast
      have hpow : (1:ℝ) ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num)
      nlinarith [ih,hpow]

private theorem corr_sqrt_coefficient0_cap (k : ℕ) :
    Real.sqrt (bandDensityCoefficient 4 k 0) ≤
      (10000:ℝ)*(3:ℝ)^k := by
  let t : ℝ := (3:ℝ)^k
  have ht : 1≤t := by dsimp [t]; exact one_le_pow₀ (by norm_num)
  have ht2 : t≤t^2 := by nlinarith [sq_nonneg (t-1)]
  have ht2one : 1≤t^2 := by nlinarith [sq_nonneg (t-1)]
  have ht4 : t≤t^4 := by
    have hh := mul_le_mul_of_nonneg_left ht2one (sq_nonneg t)
    nlinarith [hh]
  have hP : bandOrderMajorant k=64*t := by rfl
  have hvar : uniformDensityVariance 4=1000000000 := by
    norm_num [uniformDensityVariance]
  have hroot : Real.sqrt (bandOrderMajorant k*63^2*
      uniformDensityVariance 4) ≤ (25000000:ℝ)*t^2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [hP,hvar]
      calc
        _ = (254016000000000:ℝ)*t := by ring
        _ ≤ (254016000000000:ℝ)*t^4 :=
          mul_le_mul_of_nonneg_left ht4 (by norm_num)
        _ ≤ ((25000000:ℝ)*t^2)^2 := by nlinarith [sq_nonneg (t^2)]
  have hcoeffEq : bandDensityCoefficient 4 k 0 =
      4*Real.sqrt (bandOrderMajorant k*63^2*uniformDensityVariance 4) := by
    simp [bandDensityCoefficient]
  have hcoeff : bandDensityCoefficient 4 k 0 ≤ ((10000:ℝ)*t)^2 := by
    rw [hcoeffEq]
    calc
      _ ≤ (100000000:ℝ)*t^2 := by nlinarith [hroot]
      _ = ((10000:ℝ)*t)^2 := by ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa [t] using hcoeff

private theorem corr_sqrt_coefficient1_cap (k : ℕ) :
    Real.sqrt (bandDensityCoefficient 4 k 1) ≤
      (150000:ℝ)*(3:ℝ)^k := by
  let t : ℝ := (3:ℝ)^k
  have ht : 1≤t := by dsimp [t]; exact one_le_pow₀ (by norm_num)
  have ht2 : t≤t^2 := by nlinarith [sq_nonneg (t-1)]
  have heq : bandDensityCoefficient 4 k 1 = 21069103104*t := by
    simp [bandDensityCoefficient,bandOrderMajorant,t]
    ring_nf
  have hcoeff : bandDensityCoefficient 4 k 1 ≤ ((150000:ℝ)*t)^2 := by
    rw [heq]
    calc
      _ ≤ (22500000000:ℝ)*t := by gcongr; norm_num
      _ ≤ 22500000000*t^2 := mul_le_mul_of_nonneg_left ht2 (by norm_num)
      _ = ((150000:ℝ)*t)^2 := by ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa [t] using hcoeff

private theorem corr_sqrt_coefficient2_cap (k : ℕ) :
    Real.sqrt (bandDensityCoefficient 4 k 2) ≤ (3:ℝ)^k := by
  have hloc := density_localization_coefficient_cap4 k
  have hpow : (9:ℝ)^k=((3:ℝ)^k)^2 := by
    calc
      (9:ℝ)^k = ((3:ℝ)^2)^k := by norm_num
      _ = (3:ℝ)^(2*k) := by rw [← pow_mul]
      _ = (3:ℝ)^(k*2) := by rw [Nat.mul_comm]
      _ = ((3:ℝ)^k)^2 := by rw [pow_mul]
  have heq : bandDensityCoefficient 4 k 2=
      bandLocalizationCoefficient 4 k := by
    simp [bandDensityCoefficient]
  rw [heq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [hpow] at hloc
    exact hloc

private theorem corr_sqrt_coefficient_cap (k : ℕ) (i : Fin 3) :
    Real.sqrt (bandDensityCoefficient 4 k i) ≤
      (150000:ℝ)*(3:ℝ)^k := by
  fin_cases i
  · calc
      _ ≤ 10000*(3:ℝ)^k := corr_sqrt_coefficient0_cap k
      _ ≤ 150000*(3:ℝ)^k := by nlinarith [show 0≤(3:ℝ)^k by positivity]
  · exact corr_sqrt_coefficient1_cap k
  · calc
      _ ≤ (3:ℝ)^k := corr_sqrt_coefficient2_cap k
      _ ≤ 150000*(3:ℝ)^k := by nlinarith [show 0≤(3:ℝ)^k by positivity]

private theorem corr_density_offset_cap (i : Fin 3) :
    1+(3:ℝ)^(densityPERate 4 i/2)+
      (3:ℝ)^(densityPERate 4 i) ≤ if i=2 then 13 else 6 := by
  fin_cases i
  · norm_num [densityPERate]
    have hhalf : (3:ℝ)^(5/12:ℝ) ≤ Real.sqrt 3 := by
      rw [Real.sqrt_eq_rpow]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      norm_num
    have hsqrt : Real.sqrt 3 ≤ 7/4 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> norm_num
    have hpow : (3:ℝ)^(5/6:ℝ)=((3:ℝ)^(5/12:ℝ))^2 := by
      rw [← Real.rpow_natCast ((3:ℝ)^(5/12:ℝ)) 2,
        ← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
      congr 1
      norm_num
    have hsq := mul_le_mul hhalf hhalf
      (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) _) (Real.sqrt_nonneg _)
    rw [hpow]
    have hsqrt2 := mul_le_mul hsqrt hsqrt (Real.sqrt_nonneg _) (by norm_num)
    nlinarith [hsq,hsqrt2]
  · norm_num [densityPERate]
    rw [← Real.sqrt_eq_rpow]
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> norm_num
    linarith
  · norm_num [densityPERate]

private theorem corr_weighted_coefficient_cap (k : ℕ) :
    (∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
      (1+(3:ℝ)^(densityPERate 4 i/2)+
        (3:ℝ)^(densityPERate 4 i))) ≤ (1000000:ℝ)*(3:ℝ)^k := by
  have h0 : Real.sqrt (bandDensityCoefficient 4 k 0)*
      (1+(3:ℝ)^(densityPERate 4 0/2)+
        (3:ℝ)^(densityPERate 4 0)) ≤ 60000*(3:ℝ)^k := by
    have hc := corr_sqrt_coefficient0_cap k
    have ho := corr_density_offset_cap 0
    calc
      _ ≤ (10000*(3:ℝ)^k)*
          (1+(3:ℝ)^(densityPERate 4 0/2)+
            (3:ℝ)^(densityPERate 4 0)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (10000*(3:ℝ)^k)*6 := mul_le_mul_of_nonneg_left ho (by norm_num)
      _ = 60000*(3:ℝ)^k := by ring
  have h1 : Real.sqrt (bandDensityCoefficient 4 k 1)*
      (1+(3:ℝ)^(densityPERate 4 1/2)+
        (3:ℝ)^(densityPERate 4 1)) ≤ 900000*(3:ℝ)^k := by
    have hc := corr_sqrt_coefficient_cap k 1
    have ho := corr_density_offset_cap 1
    calc
      _ ≤ (150000*(3:ℝ)^k)*
          (1+(3:ℝ)^(densityPERate 4 1/2)+
            (3:ℝ)^(densityPERate 4 1)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (150000*(3:ℝ)^k)*6 := mul_le_mul_of_nonneg_left ho (by norm_num)
      _ = 900000*(3:ℝ)^k := by ring
  have h2 : Real.sqrt (bandDensityCoefficient 4 k 2)*
      (1+(3:ℝ)^(densityPERate 4 2/2)+
        (3:ℝ)^(densityPERate 4 2)) ≤ 13*(3:ℝ)^k := by
    have hc : Real.sqrt (bandDensityCoefficient 4 k 2) ≤ (3:ℝ)^k := by
      have hloc := density_localization_coefficient_cap4 k
      have hpow : (9:ℝ)^k=((3:ℝ)^k)^2 := by
        calc
          (9:ℝ)^k = ((3:ℝ)^2)^k := by norm_num
          _ = (3:ℝ)^(2*k) := by rw [← pow_mul]
          _ = (3:ℝ)^(k*2) := by rw [Nat.mul_comm]
          _ = ((3:ℝ)^k)^2 := by rw [pow_mul]
      have heq : bandDensityCoefficient 4 k 2=
          bandLocalizationCoefficient 4 k := by simp [bandDensityCoefficient]
      rw [heq]
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [hpow] at hloc
        exact hloc
    have ho := corr_density_offset_cap 2
    calc
      _ ≤ (3:ℝ)^k*
          (1+(3:ℝ)^(densityPERate 4 2/2)+
            (3:ℝ)^(densityPERate 4 2)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ (3:ℝ)^k*13 := mul_le_mul_of_nonneg_left ho (by positivity)
      _ = 13*(3:ℝ)^k := by ring
  have hsum :
      (∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i))) ≤
        ∑ i : Fin 3, (if i=0 then 60000*(3:ℝ)^k
          else if i=1 then 900000*(3:ℝ)^k else 13*(3:ℝ)^k) := by
    apply Finset.sum_le_sum
    intro i hi
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  calc
    _ ≤ ∑ i : Fin 3, (if i=0 then 60000*(3:ℝ)^k
        else if i=1 then 900000*(3:ℝ)^k else 13*(3:ℝ)^k) := hsum
    _ = 960013*(3:ℝ)^k := by norm_num [Fin.sum_univ_succ]; ring
    _ ≤ 1000000*(3:ℝ)^k := by nlinarith [show 0≤(3:ℝ)^k by positivity]

private theorem corr_reset_profile (γ : ℝ) (hγ : γ ≤ gammaZero)
    (k : ℕ) (i : Fin 3) :
    densityResetPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k) ≤
        9*(3:ℝ)^(-(143+4*k:ℕ):ℝ) ∧
      densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k) ≤
        3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k := by
  let C := 344+12*k
  let N := 143+4*k
  let β : ℝ := 83/200
  let c : ℝ := 13/20
  have hγ' : γ ≤ 17/50000 := by simpa [gammaZero] using hγ
  have hrate : 0 ≤ β := by norm_num [β]
  have hc : 0 ≤ c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  have hq : (3:ℝ)^(-β) ≤ c := by
    have hexp : -β ≤ -(2/5:ℝ) := by norm_num [β]
    have h40 := full_response_three_neg_40_le
    have h40' : (3:ℝ)^(-(2/5:ℝ)) ≤ (13/20:ℝ) := by
      norm_num at h40 ⊢
      exact h40
    calc
      _ ≤ (3:ℝ)^(-(2/5:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hexp
      _ ≤ c := by simpa [c] using h40'
  have hN : (N:ℝ) ≤ β*((C+1:ℕ):ℝ) := by
    dsimp [N,β,C]
    push_cast
    nlinarith
  have hdecay : 4*γ < densityPERate 4 i/2 := by
    fin_cases i <;> norm_num [densityPERate] <;> nlinarith [hγ']
  have hβ : β ≤ densityPERate 4 i/2-4*γ := by
    fin_cases i <;> norm_num [β,densityPERate] <;> nlinarith [hγ']
  have hraw := full_response_retained_reset_bounds
    (4*γ) (densityPERate 4 i/2) β c C N hdecay hβ hrate hN hc hc1 hq
  have hν0 : 0 ≤ densityPERate 4 i/2 := by
    fin_cases i <;> norm_num [densityPERate]
  have hνpow : (3:ℝ)^(-(densityPERate 4 i/2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1:ℝ)≤3) (by linarith [hν0])
  have hgeom : (1/(1-c))^2 ≤ 9 := by norm_num [c]
  have hgeomFirst :
      (((C:ℝ)+2)*(1/(1-c))^2+3*c/(1-c)^3) ≤ 3000*(3:ℝ)^k := by
    have hC : (C:ℝ)=344+12*(k:ℝ) := by dsimp [C]; norm_num
    have hlin := corr_linear_le_power k
    have hpow : 1 ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
    have hsmall :
        ((C:ℝ)+2)*(1/(1-c))^2+3*c/(1-c)^3 ≤ 2900+100*(k:ℝ) := by
      norm_num [c]
      nlinarith [hC]
    nlinarith [hsmall,hlin,hpow]
  constructor
  · calc
      _ ≤ (3:ℝ)^(-(densityPERate 4 i/2)) *
          (3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 := hraw.1
      _ ≤ 1*(3:ℝ)^(-(N:ℝ))*9 := by gcongr
      _ = 9*(3:ℝ)^(-(143+4*k:ℕ):ℝ) := by dsimp [N]; ring
  · calc
      _ ≤ (3:ℝ)^(-(densityPERate 4 i/2)) *
          (3:ℝ)^(-(N:ℝ))*
            (((C:ℝ)+2)*(1/(1-c))^2+3*c/(1-c)^3) := hraw.2
      _ ≤ 1*(3:ℝ)^(-(N:ℝ))*(3000*(3:ℝ)^k) := by gcongr
      _ = 3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k := by dsimp [C,N]; ring

private theorem corr_reset_nonneg (γ : ℝ) (hγ : γ≤gammaZero)
    (k : ℕ) (i : Fin 3) :
    0 ≤ densityResetPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k) ∧
      0 ≤ densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k) := by
  have hγ' : γ≤17/50000 := by simpa [gammaZero] using hγ
  have hdecay : 4*γ<densityPERate 4 i/2 := by
    fin_cases i <;> norm_num [densityPERate] <;> nlinarith [hγ']
  have hs := density_reset_power_hasSum (4*γ) (densityPERate 4 i/2)
    hdecay (344+12*k)
  have hs1 := density_reset_first_power_hasSum (4*γ)
    (densityPERate 4 i/2) hdecay (344+12*k)
  constructor
  · rw [← hs.tsum_eq]
    apply tsum_nonneg
    intro hk
    positivity
  · rw [← hs1.tsum_eq]
    apply tsum_nonneg
    intro hk
    positivity

private theorem corr_density_sum_power_nonneg (γ : ℝ) (hγ : γ≤gammaZero)
    (k : ℕ) (S : ℝ) (hS : 0≤S) :
    0≤bandDensitySum4 k γ S (344+12*k) 0 := by
  have hreset (i : Fin 3) := (corr_reset_nonneg γ hγ k i).1
  unfold bandDensitySum4
  simp only [Fin.isValue, ↓reduceIte]
  apply mul_nonneg (by linarith)
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (by positivity)) (hreset i)

private theorem corr_density_sum_first_nonneg (γ : ℝ) (hγ : γ≤gammaZero)
    (k : ℕ) :
    0≤bandDensitySum4 k γ 0 (344+12*k) 1 := by
  have hreset (i : Fin 3) := (corr_reset_nonneg γ hγ k i).2
  unfold bandDensitySum4
  simp only [Fin.isValue, one_ne_zero, ite_false, zero_add, one_mul]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (by positivity)) (hreset i)

private theorem corr_band_decay (k : ℕ) :
    (3:ℝ)^k*(3:ℝ)^(-(143+4*k:ℕ):ℝ) ≤ (3:ℝ)^(-143:ℝ) := by
  have hN : ((143+4*k:ℕ):ℝ)=143+4*(k:ℝ) := by norm_num
  have heq : (3:ℝ)^k*(3:ℝ)^(-(143+4*k:ℕ):ℝ) =
      (3:ℝ)^(-143-3*(k:ℝ)) := by
    rw [hN,← Real.rpow_natCast (3:ℝ) k,
      ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (by nlinarith [show 0≤(k:ℝ) by positivity])

private theorem corr_band_decay_two (k : ℕ) :
    (3:ℝ)^(2*k)*(3:ℝ)^(-(143+4*k:ℕ):ℝ) ≤ (3:ℝ)^(-143:ℝ) := by
  have hN : ((143+4*k:ℕ):ℝ)=143+4*(k:ℝ) := by norm_num
  have heq : (3:ℝ)^(2*k)*(3:ℝ)^(-(143+4*k:ℕ):ℝ) =
      (3:ℝ)^(-143-2*(k:ℝ)) := by
    rw [hN,← Real.rpow_natCast (3:ℝ) (2*k),
      ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    push_cast
    ring
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (by nlinarith [show 0≤(k:ℝ) by positivity])

private theorem corr_density_sum_power_cap (γ : ℝ) (hγ : γ≤gammaZero)
    (k : ℕ) (S : ℝ) (hS : 0≤S) :
    bandDensitySum4 k γ S (344+12*k) 0 ≤
      9000000*(S+1)*(3:ℝ)^(-143:ℝ) := by
  have hcoeff := corr_weighted_coefficient_cap k
  have hreset (i : Fin 3) := (corr_reset_profile γ hγ k i).1
  have hterm (i : Fin 3) :
      Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i))*
        densityResetPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k) ≤
      (Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i)))*
        (9*(3:ℝ)^(-(143+4*k:ℕ):ℝ)) := by
    exact mul_le_mul_of_nonneg_left (hreset i)
      (by positivity)
  have hsum :
      (∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i))*
        densityResetPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k)) ≤
      (9*(3:ℝ)^(-(143+4*k:ℕ):ℝ))*((1000000:ℝ)*(3:ℝ)^k) := by
    calc
      _ ≤ ∑ i : Fin 3,
          (Real.sqrt (bandDensityCoefficient 4 k i)*
            (1+(3:ℝ)^(densityPERate 4 i/2)+
              (3:ℝ)^(densityPERate 4 i))*
            (9*(3:ℝ)^(-(143+4*k:ℕ):ℝ))) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (9*(3:ℝ)^(-(143+4*k:ℕ):ℝ))*
          (∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
            (1+(3:ℝ)^(densityPERate 4 i/2)+
              (3:ℝ)^(densityPERate 4 i))) := by rw [← Finset.sum_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff (by positivity)
  have hdecay := corr_band_decay k
  unfold bandDensitySum4
  simp only [Fin.isValue, ↓reduceIte]
  calc
    _ ≤ (S+1)*((9*(3:ℝ)^(-(143+4*k:ℕ):ℝ))*
        ((1000000:ℝ)*(3:ℝ)^k)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 9000000*(S+1)*
        ((3:ℝ)^k*(3:ℝ)^(-(143+4*k:ℕ):ℝ)) := by ring
    _ ≤ 9000000*(S+1)*(3:ℝ)^(-143:ℝ) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)

private theorem corr_density_sum_first_cap (γ : ℝ) (hγ : γ≤gammaZero)
    (k : ℕ) :
    bandDensitySum4 k γ 0 (344+12*k) 1 ≤
      3000000000*(3:ℝ)^(-143:ℝ) := by
  have hcoeff := corr_weighted_coefficient_cap k
  have hreset (i : Fin 3) := (corr_reset_profile γ hγ k i).2
  have hterm (i : Fin 3) :
      Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i))*
        densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k) ≤
      (Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i)))*
        (3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k) := by
    exact mul_le_mul_of_nonneg_left (hreset i)
      (by positivity)
  have hsum :
      (∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
        (1+(3:ℝ)^(densityPERate 4 i/2)+
          (3:ℝ)^(densityPERate 4 i))*
        densityResetFirstPowerSum (4*γ) (densityPERate 4 i/2) (344+12*k)) ≤
      (3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k)*
        ((1000000:ℝ)*(3:ℝ)^k) := by
    calc
      _ ≤ ∑ i : Fin 3,
          (Real.sqrt (bandDensityCoefficient 4 k i)*
            (1+(3:ℝ)^(densityPERate 4 i/2)+
              (3:ℝ)^(densityPERate 4 i))*
            (3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k)*
          (∑ i : Fin 3, Real.sqrt (bandDensityCoefficient 4 k i)*
            (1+(3:ℝ)^(densityPERate 4 i/2)+
              (3:ℝ)^(densityPERate 4 i))) := by rw [← Finset.sum_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff (by positivity)
  have hdecay := corr_band_decay_two k
  unfold bandDensitySum4
  simp only [Fin.isValue, one_ne_zero, ite_false, zero_add, one_mul]
  have hpow : (3:ℝ)^k*(3:ℝ)^k=(3:ℝ)^(2*k) := by
    have hkk : k+k=2*k := by omega
    rw [← hkk,← pow_add]
  calc
    _ ≤ (3000*(3:ℝ)^(-(143+4*k:ℕ):ℝ)*(3:ℝ)^k)*
        ((1000000:ℝ)*(3:ℝ)^k) := hsum
    _ = 3000000000*((3:ℝ)^(2*k)*
        (3:ℝ)^(-(143+4*k:ℕ):ℝ)) := by rw [← hpow]; ring
    _ ≤ 3000000000*(3:ℝ)^(-143:ℝ) :=
      mul_le_mul_of_nonneg_left hdecay (by norm_num)

private theorem corr_coefficient_cap :
    0 ≤ assemblyTraceCorrelationCoefficient ∧
      assemblyTraceCorrelationCoefficient ≤ (5*10^58:ℝ) := by
  have hsens := assembly_sensitivity_lt
  have hresponse := assembly_trace_response_coefficient_bound
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hresponse0 : 0 ≤ 1+2*Real.sqrt 3*resetAllOrderTau := by positivity
  have hcharge0 : 0 ≤ planarGradientCharge 40+1 := by
    norm_num [planarGradientCharge]
  have hcharge : planarGradientCharge 40+1 ≤ 4*10^41 := by
    norm_num [planarGradientCharge]
  have hsens0 : 0 ≤ rootAssemblySensitivity :=
    root_assembly_sensitivity_pos.le
  have hprod : rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau) ≤
      (127/100:ℝ)*(2*10^16) :=
    mul_le_mul hsens.le hresponse.le hresponse0 (by norm_num)
  constructor
  · unfold assemblyTraceCorrelationCoefficient
    positivity
  · calc
      assemblyTraceCorrelationCoefficient =
          4*(rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau))*
            (planarGradientCharge 40+1) := by
        unfold assemblyTraceCorrelationCoefficient
        ring
      _ ≤ 4*((127/100:ℝ)*(2*10^16))*(planarGradientCharge 40+1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by norm_num)) hcharge0
      _ ≤ 4*((127/100:ℝ)*(2*10^16))*(4*10^41) :=
        mul_le_mul_of_nonneg_left hcharge (by norm_num)
      _ ≤ 5*10^58 := by norm_num

private theorem corr_three143_ge_ten68 :
    (10:ℝ)^68 ≤ (3:ℝ)^143 := by norm_num

private theorem corr_three_neg143_le_ten_neg68 :
    (3:ℝ)^(-143:ℝ) ≤ (10:ℝ)^(-68:ℝ) := by
  have hcast3 : (3:ℝ)^(143:ℝ)=(3:ℝ)^143 := Real.rpow_natCast _ _
  have hcast10 : (10:ℝ)^(68:ℝ)=(10:ℝ)^68 := Real.rpow_natCast _ _
  have hreal : (10:ℝ)^(68:ℝ) ≤ (3:ℝ)^(143:ℝ) := by
    rw [hcast10,hcast3]
    exact corr_three143_ge_ten68
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3),
    Real.rpow_neg (by norm_num : (0:ℝ)≤10)]
  have hinv := one_div_le_one_div_of_le (by positivity) hreal
  simpa only [one_div] using hinv

/-- The two actual D4 common-noise payments together cost at most 200 units
of the source `γ*(E+20+p*(D+1))*3^(2γD)` allowance. -/
theorem assembly_trace_correlation_profile_cap
    (γ p D : ℝ) (hγ : γ≤gammaZero) (hγ0 : 0≤γ)
    (hp : 2≤p) (hD : 0≤D) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyTraceCorrelationCoefficient*γ*(3:ℝ)^(2*γ*D)*
      (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
        40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤
      200*γ*((E:ℝ)+20+p*(D+1))*(3:ℝ)^(2*γ*D) := by
  let k := orderBand p
  let E := heightEntrance k
  let A := (E:ℝ)+20+p*(D+1)
  have hC : E+5-38=344+12*k := by
    dsimp [E,k,heightEntrance]
    omega
  have hsumD := corr_density_sum_power_cap γ hγ k D hD
  have hsum0 := corr_density_sum_first_cap γ hγ k
  have hsumD0 := corr_density_sum_power_nonneg γ hγ k D hD
  have hsum00 := corr_density_sum_first_nonneg γ hγ k
  have hsumD0' : 0≤bandDensitySum4 k γ D (E+5-38) 0 := by
    rw [hC]
    exact hsumD0
  have hsum00' : 0≤bandDensitySum4 k γ 0 (E+5-38) 1 := by
    rw [hC]
    exact hsum00
  have hsmall := corr_three_neg143_le_ten_neg68
  have hlin : 2*p+2≤3*p := by linarith
  have htermD : 40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0 ≤
      (1080000000:ℝ)*p*(D+1)*(10:ℝ)^(-68:ℝ) := by
    rw [hC]
    calc
      _ ≤ (120*p)*bandDensitySum4 k γ D (344+12*k) 0 := by
        exact mul_le_mul_of_nonneg_right
          (by nlinarith : 40*(2*p+2)≤120*p) hsumD0
      _ ≤ (120*p)*(9000000*(D+1)*(3:ℝ)^(-143:ℝ)) :=
        mul_le_mul_of_nonneg_left hsumD (by positivity)
      _ ≤ (1080000000:ℝ)*p*(D+1)*(10:ℝ)^(-68:ℝ) := by
        calc
          _ = (1080000000:ℝ)*(p*(D+1))*(3:ℝ)^(-143:ℝ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
          _ = _ := by ring
  have hterm0 : 40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1 ≤
      (360000000000:ℝ)*p*(10:ℝ)^(-68:ℝ) := by
    rw [hC]
    calc
      _ ≤ (120*p)*bandDensitySum4 k γ 0 (344+12*k) 1 := by
        exact mul_le_mul_of_nonneg_right
          (by nlinarith : 40*(2*p+2)≤120*p) hsum00
      _ ≤ (120*p)*(3000000000*(3:ℝ)^(-143:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum0 (by positivity)
      _ ≤ (360000000000:ℝ)*p*(10:ℝ)^(-68:ℝ) := by
        calc
          _ = (360000000000:ℝ)*p*(3:ℝ)^(-143:ℝ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
          _ = _ := by ring
  have hA0 : 0≤A := by dsimp [A]; positivity
  have hpA : p≤A := by dsimp [A]; nlinarith [hp,hD]
  have hpdA : p*(D+1)≤A := by dsimp [A]; nlinarith [hD]
  have hconstD : (5*10^58:ℝ)*(1080000000:ℝ)*(10:ℝ)^(-68:ℝ)≤1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤10)]
    norm_num
  have hconst0 : (5*10^58:ℝ)*(360000000000:ℝ)*(10:ℝ)^(-68:ℝ)≤180 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤10)]
    norm_num
  have hcoef := corr_coefficient_cap
  have hweightedD :
      assemblyTraceCorrelationCoefficient*
        (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0) ≤ A := by
    calc
      _ ≤ (5*10^58:ℝ)*
          (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0) :=
        mul_le_mul_of_nonneg_right hcoef.2 (mul_nonneg (by positivity) hsumD0')
      _ ≤ (5*10^58:ℝ)*
          ((1080000000:ℝ)*p*(D+1)*(10:ℝ)^(-68:ℝ)) :=
        mul_le_mul_of_nonneg_left htermD (by norm_num)
      _ = ((5*10^58:ℝ)*(1080000000:ℝ)*(10:ℝ)^(-68:ℝ))*(p*(D+1)) := by ring
      _ ≤ p*(D+1) := by
        have hfactorD : 0≤p*(D+1) :=
          mul_nonneg (by linarith [hp]) (by linarith [hD])
        exact (mul_le_mul_of_nonneg_right hconstD hfactorD).trans_eq (by ring)
      _ ≤ A := hpdA
  have hweighted0 :
      assemblyTraceCorrelationCoefficient*
        (40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤ 180*A := by
    calc
      _ ≤ (5*10^58:ℝ)*
          (40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) :=
        mul_le_mul_of_nonneg_right hcoef.2 (mul_nonneg (by positivity) hsum00')
      _ ≤ (5*10^58:ℝ)*
          ((360000000000:ℝ)*p*(10:ℝ)^(-68:ℝ)) :=
        mul_le_mul_of_nonneg_left hterm0 (by norm_num)
      _ = ((5*10^58:ℝ)*(360000000000:ℝ)*(10:ℝ)^(-68:ℝ))*p := by ring
      _ ≤ 180*p := by
        have hp0 : 0≤p := by linarith [hp]
        exact (mul_le_mul_of_nonneg_right hconst0 hp0).trans_eq (by ring)
      _ ≤ 180*A := mul_le_mul_of_nonneg_left hpA (by norm_num)
  have hsum :
      assemblyTraceCorrelationCoefficient*
        (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
          40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤ 200*A := by
    calc
      _ = assemblyTraceCorrelationCoefficient*
            (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0)+
          assemblyTraceCorrelationCoefficient*
            (40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) := by ring
      _ ≤ A+180*A := add_le_add hweightedD hweighted0
      _ ≤ 200*A := by nlinarith [hA0]
  have hfactor : 0≤γ*(3:ℝ)^(2*γ*D) :=
    mul_nonneg hγ0 (Real.rpow_nonneg (by norm_num) _)
  change assemblyTraceCorrelationCoefficient*γ*(3:ℝ)^(2*γ*D)*
      (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
        40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1) ≤
      200*γ*A*(3:ℝ)^(2*γ*D)
  calc
    _ = γ*(3:ℝ)^(2*γ*D)*
        (assemblyTraceCorrelationCoefficient*
          (40*(2*p+2)*bandDensitySum4 k γ D (E+5-38) 0+
            40*(2*p+2)*bandDensitySum4 k γ 0 (E+5-38) 1)) := by ring
    _ ≤ γ*(3:ℝ)^(2*γ*D)*(200*A) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = 200*γ*A*(3:ℝ)^(2*γ*D) := by ring

end
end ASDExplicitGamma.Inverse


