module

public import ASDExplicitGamma.Inverse.AssemblyTraceMatrixBudget
public import ASDExplicitGamma.Inverse.AssemblyMatrixBandProfile
public import ASDExplicitGamma.Inverse.AssemblyTraceNumerics

/-! Numerical profile cap for the complete trace-matrix error series. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
noncomputable section

private theorem matrix_profile_three336_ge_pow30 :
    (10:ℝ)^30 ≤ (3:ℝ)^336 := by
  have hbase : (10:ℝ) ≤ (3:ℝ)^3 := by norm_num
  calc
    _ ≤ ((3:ℝ)^3)^30 := pow_le_pow_left₀ (by norm_num) hbase 30
    _ = (3:ℝ)^(3*30) := by rw [← pow_mul]
    _ ≤ (3:ℝ)^336 :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3) (by norm_num)

private theorem matrix_profile_three336_ge_pow30_rpow :
    (10:ℝ)^30 ≤ (3:ℝ)^(336:ℝ) := by
  have h := matrix_profile_three336_ge_pow30
  change (10:ℝ)^30 ≤ (3:ℝ)^((336:ℕ):ℝ)
  rw [Real.rpow_natCast]
  exact h

private theorem matrix_profile_small_power :
    (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ) ≤ 1/100 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
  have hden : ((3:ℝ)^(336:ℝ))⁻¹ ≤ ((10:ℝ)^30)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity)
      matrix_profile_three336_ge_pow30_rpow
  calc
    _ ≤ (896*10^18:ℝ)/(10:ℝ)^30 := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ 1/100 := by norm_num

private theorem matrix_profile_small_order_power :
    ((1120*10^18:ℝ)*4096)*(3:ℝ)^(-336:ℝ) ≤ 1 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
  have hden : ((3:ℝ)^(336:ℝ))⁻¹ ≤ ((10:ℝ)^30)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity)
      matrix_profile_three336_ge_pow30_rpow
  calc
    _ ≤ ((1120*10^18:ℝ)*4096)/(10:ℝ)^30 := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ 1 := by norm_num

/-- The matrix reset budget is a tiny baseline term plus one unit of the
source `γ*(h+20+p*(D+1))` allowance. This retains the exact order band,
terminal depth, and source first-abscissa moment. -/
theorem assembly_trace_matrix_profile_cap
    (γ p D : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ)
    (hp : 2 ≤ p) (hD : 0 ≤ D) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyTraceMatrixBudget γ p D (E+5) ≤
      1/100 + γ*((E:ℝ)+20+p*(D+1))*(3:ℝ)^(2*γ*D) := by
  let k := orderBand p
  let E := heightEntrance k
  let C := 344+12*k
  let N := 336+11*k
  let A := (E:ℝ)+20+p*(D+1)
  have hp0 : 0 ≤ p := by linarith only [hp]
  have horder := order_band_scale p
  have horder' : p ≤ 64*(3:ℝ)^k := by simpa using horder
  have hC : (C:ℝ) = 344+12*(k:ℝ) := by dsimp [C]; norm_num
  have hN : (N:ℝ) = 336+11*(k:ℝ) := by dsimp [N]; norm_num
  have hreset := assembly_trace_reset_profile_bounds γ hγ k
  have hreset2 : densityResetPowerSum (2*γ) 1 C ≤
      (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100))^2 := by
    simpa [C,N] using hreset.1
  have hreset4 : densityResetPowerSum (4*γ) 1 C ≤
      (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100))^2 := by
    simpa [C,N] using hreset.2.1
  have hfirst : densityResetFirstPowerSum (4*γ) 1 C ≤
      (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*
        (((C:ℝ)+2)*(1/(1-34/100))^2+
          3*(34/100)/(1-34/100)^3) := by
    simpa [C,N] using hreset.2.2
  have hdecay1 : p*(3:ℝ)^(-(N:ℝ)) ≤ 64*(3:ℝ)^(-336:ℝ) := by
    calc
      _ ≤ (64*(3:ℝ)^k)*(3:ℝ)^(-(N:ℝ)) :=
        mul_le_mul_of_nonneg_right horder' (by positivity)
      _ = 64*((3:ℝ)^k*(3:ℝ)^(-(N:ℝ))) := by ring
      _ ≤ 64*(3:ℝ)^(-336:ℝ) := by
        rw [hN,← Real.rpow_natCast (3:ℝ) k]
        have hmul :
            (3:ℝ)^(k:ℝ)*(3:ℝ)^(-(336+11*(k:ℝ))) =
              (3:ℝ)^((k:ℝ)-(336+11*(k:ℝ))) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
          congr 1
        rw [hmul]
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) (by nlinarith)
        · norm_num
  have hdecay2 : p^2*(3:ℝ)^(-(N:ℝ)) ≤ 4096*(3:ℝ)^(-336:ℝ) := by
    have hsq : p*p ≤ (64*(3:ℝ)^k)*(64*(3:ℝ)^k) :=
      mul_le_mul horder' horder' hp0 (by positivity)
    calc
      _ = (p*p)*(3:ℝ)^(-(N:ℝ)) := by ring
      _ ≤ ((64*(3:ℝ)^k)*(64*(3:ℝ)^k))*(3:ℝ)^(-(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 4096*((3:ℝ)^(2*k))*(3:ℝ)^(-(N:ℝ)) := by
        calc
          _ = 4096*((3:ℝ)^k*(3:ℝ)^k)*(3:ℝ)^(-(N:ℝ)) := by ring
          _ = 4096*(3:ℝ)^(k+k)*(3:ℝ)^(-(N:ℝ)) := by rw [← pow_add]
          _ = _ := by rw [show k+k=2*k by omega]
      _ ≤ 4096*(3:ℝ)^(-336:ℝ) := by
        have hrewrite :
            (3:ℝ)^(2*k:ℕ)*(3:ℝ)^(-(N:ℝ)) =
              (3:ℝ)^(2*(k:ℝ)-(336+11*(k:ℝ))) := by
          rw [hN,← Real.rpow_natCast (3:ℝ) (2*k),← Real.rpow_add (by norm_num : (0:ℝ)<3)]
          congr 1
          push_cast
          ring
        calc
          _ = 4096*((3:ℝ)^(2*k:ℕ)*(3:ℝ)^(-(N:ℝ))) := by ring
          _ = 4096*(3:ℝ)^(2*(k:ℝ)-(336+11*(k:ℝ))) := by rw [hrewrite]
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left
            · exact Real.rpow_le_rpow_of_exponent_le
                (by norm_num : (1:ℝ)≤3) (by nlinarith)
            · norm_num
  have hpow2 :
      (3:ℝ)^(-1:ℝ)*(1/(1-34/100:ℝ))^2 ≤ 1 := by norm_num
  have hpow4 :
      (3:ℝ)^(-1:ℝ)*
        (((C:ℝ)+2)*(1/(1-34/100:ℝ))^2+
          3*(34/100)/(1-34/100)^3) ≤ (C:ℝ)+5 := by
    have hC0 : 0 ≤ (C:ℝ) := by positivity
    norm_num
    nlinarith [hC0]
  have hsum2 : densityResetPowerSum (2*γ) 1 C ≤ (3:ℝ)^(-(N:ℝ)) := by
    calc
      _ ≤ (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100))^2 := hreset2
      _ = ((3:ℝ)^(-1:ℝ)*(1/(1-34/100:ℝ))^2)*(3:ℝ)^(-(N:ℝ)) := by ring
      _ ≤ 1*(3:ℝ)^(-(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hpow2 (by positivity)
      _ = _ := by ring
  have hsum4 : densityResetPowerSum (4*γ) 1 C ≤ (3:ℝ)^(-(N:ℝ)) := by
    calc
      _ ≤ (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100))^2 := hreset4
      _ = ((3:ℝ)^(-1:ℝ)*(1/(1-34/100:ℝ))^2)*(3:ℝ)^(-(N:ℝ)) := by ring
      _ ≤ 1*(3:ℝ)^(-(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hpow2 (by positivity)
      _ = _ := by ring
  have hfirst' : densityResetFirstPowerSum (4*γ) 1 C ≤
      ((C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)) := by
    calc
      _ ≤ (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*
        (((C:ℝ)+2)*(1/(1-34/100))^2+
          3*(34/100)/(1-34/100)^3) := hfirst
      _ ≤ ((C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)) := by
        calc
          _ = ((3:ℝ)^(-1:ℝ)*
              (((C:ℝ)+2)*(1/(1-34/100:ℝ))^2+
                3*(34/100)/(1-34/100)^3))*(3:ℝ)^(-(N:ℝ)) := by ring
          _ ≤ ((C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)) :=
            mul_le_mul_of_nonneg_right hpow4 (by positivity)
  have htau0 : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hresp : rootResponseEnvelope resetAllOrderTau < 2*10^16 := by
    unfold rootResponseEnvelope
    have htau' : resetAllOrderTau ≤ 6*10^15 := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hrad : Real.sqrt (resetAllOrderTau*(resetAllOrderTau+2)) ≤
        resetAllOrderTau+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [htau0]
    nlinarith [htau0,htau',hrad]
  have hresp0 : 0 ≤ rootResponseEnvelope resetAllOrderTau := by
    unfold rootResponseEnvelope
    exact add_nonneg (add_nonneg (by norm_num) htau0)
      (Real.sqrt_nonneg _)
  have hsqrtp : Real.sqrt p ≤ p := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hp]
    · nlinarith only [hp]
  have hpref :
      rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau ≤
        (7*10^18:ℝ)*p := by
    calc
      _ ≤ (127/100:ℝ)*256*Real.sqrt p*(2*10^16) := by
        have hsens := assembly_sensitivity_lt
        have hfirst : rootAssemblySensitivity*256*Real.sqrt p ≤
            (127/100:ℝ)*256*Real.sqrt p :=
          calc
            _ = rootAssemblySensitivity*(256*Real.sqrt p) := by ring
            _ ≤ (127/100:ℝ)*(256*Real.sqrt p) :=
              mul_le_mul_of_nonneg_right hsens.le (by positivity)
            _ = _ := by ring
        calc
          _ = (rootAssemblySensitivity*256*Real.sqrt p)*
              rootResponseEnvelope resetAllOrderTau := by ring
          _ ≤ ((127/100:ℝ)*256*Real.sqrt p)*
              rootResponseEnvelope resetAllOrderTau :=
            mul_le_mul_of_nonneg_right hfirst hresp0
          _ ≤ ((127/100:ℝ)*256*Real.sqrt p)*(2*10^16) :=
            mul_le_mul_of_nonneg_left (le_of_lt hresp) (by positivity)
          _ = _ := by ring
      _ ≤ (7*10^18:ℝ)*p := by
        have hsqrt := hsqrtp
        nlinarith [hsqrt]
  have hbaseSmall := matrix_profile_small_power
  have horderSmall := matrix_profile_small_order_power
  have hCbound : (C:ℝ)+5 ≤ (E:ℝ)+20 := by
    dsimp [E,heightEntrance,C]
    norm_num
    linarith
  have hDCA : D+(C:ℝ)+5 ≤ A := by
    have hDle : D ≤ p*D := by nlinarith [hD,hp]
    dsimp [A]
    nlinarith [hCbound,hDle,mul_nonneg hp0 hD]
  have hmain :
      assemblyTraceMatrixBudget γ p D (E+5) ≤
        (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ) +
          ((1120*10^18:ℝ)*4096)*(3:ℝ)^(-336:ℝ)*
            (γ*A*(3:ℝ)^(2*γ*D)) := by
    unfold assemblyTraceMatrixBudget
    have hCnat : E+5-38=C := by dsimp [E,C,heightEntrance]; omega
    rw [hCnat]
    have hpPlus : p+2 ≤ 2*p := by linarith only [hp]
    have hsumD : D*densityResetPowerSum (4*γ) 1 C+
        densityResetFirstPowerSum (4*γ) 1 C ≤
          (D+(C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)) := by
      calc
        _ ≤ D*(3:ℝ)^(-(N:ℝ))+((C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hsum4 hD) hfirst'
        _ = _ := by ring
    have hbase :
        2*densityResetPowerSum (2*γ) 1 C ≤ 2*(3:ℝ)^(-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum2 (by norm_num)
    have hbracket :
        2*densityResetPowerSum (2*γ) 1 C+
          80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
            (D*densityResetPowerSum (4*γ) 1 C+
              densityResetFirstPowerSum (4*γ) 1 C) ≤
        2*(3:ℝ)^(-(N:ℝ))+
          80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
            ((D+(C:ℝ)+5)*(3:ℝ)^(-(N:ℝ))) := by
      exact add_le_add hbase
        (mul_le_mul_of_nonneg_left hsumD (by positivity))
    have hpref0 : 0 ≤ rootAssemblySensitivity*256*Real.sqrt p*
        rootResponseEnvelope resetAllOrderTau :=
      mul_nonneg (mul_nonneg (mul_nonneg root_assembly_sensitivity_pos.le
        (by norm_num)) (Real.sqrt_nonneg _)) hresp0
    calc
      _ ≤ ((7*10^18:ℝ)*p)*
          (2*(3:ℝ)^(-(N:ℝ))+
            80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
              ((D+(C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)))) := by
        calc
          _ ≤ (rootAssemblySensitivity*256*Real.sqrt p*
              rootResponseEnvelope resetAllOrderTau)*
              (2*(3:ℝ)^(-(N:ℝ))+
                80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
                  ((D+(C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)))) :=
            mul_le_mul_of_nonneg_left hbracket hpref0
          _ ≤ _ :=
            mul_le_mul_of_nonneg_right hpref (by positivity)
      _ ≤ (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ)+
          ((1120*10^18:ℝ)*4096)*(3:ℝ)^(-336:ℝ)*
            (γ*A*(3:ℝ)^(2*γ*D)) := by
        have hterm0 :
            (7*10^18:ℝ)*p*(2*(3:ℝ)^(-(N:ℝ))) ≤
              (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ) := by
          calc
            _ = (14*10^18:ℝ)*(p*(3:ℝ)^(-(N:ℝ))) := by ring
            _ ≤ (14*10^18:ℝ)*(64*(3:ℝ)^(-336:ℝ)) :=
              mul_le_mul_of_nonneg_left hdecay1 (by norm_num)
            _ = _ := by ring
        have hterm1 :
            (7*10^18:ℝ)*p*(80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
                ((D+(C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)))) ≤
              ((1120*10^18:ℝ)*4096)*(3:ℝ)^(-336:ℝ)*
                (γ*A*(3:ℝ)^(2*γ*D)) := by
          calc
            _ ≤ ((1120*10^18:ℝ))*(p^2*(3:ℝ)^(-(N:ℝ)))*
                (γ*(D+(C:ℝ)+5)*(3:ℝ)^(2*γ*D)) := by
              have horderTerm : (7*10^18:ℝ)*p*(80*(p+2)) ≤
                  (1120*10^18:ℝ)*p^2 := by
                have hfactor : 0 ≤ (7*10^18:ℝ)*p*80 := by positivity
                calc
                  _ = ((7*10^18:ℝ)*p*80)*(p+2) := by ring
                  _ ≤ ((7*10^18:ℝ)*p*80)*(2*p) :=
                    mul_le_mul_of_nonneg_left hpPlus hfactor
                  _ = _ := by ring
              have hrest : 0 ≤ γ*(D+(C:ℝ)+5)*(3:ℝ)^(2*γ*D) := by positivity
              calc
                _ = ((7*10^18:ℝ)*p*(80*(p+2)))*
                    (γ*(D+(C:ℝ)+5)*(3:ℝ)^(2*γ*D))*(3:ℝ)^(-(N:ℝ)) := by ring
                _ ≤ ((1120*10^18:ℝ)*p^2)*
                    (γ*(D+(C:ℝ)+5)*(3:ℝ)^(2*γ*D))*(3:ℝ)^(-(N:ℝ)) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right horderTerm hrest) (by positivity)
                _ = _ := by ring
            _ ≤ ((1120*10^18:ℝ))*(4096*(3:ℝ)^(-336:ℝ))*
                (γ*A*(3:ℝ)^(2*γ*D)) := by
              have hfirstFactor :
                  (1120*10^18:ℝ)*(p^2*(3:ℝ)^(-(N:ℝ))) ≤
                    (1120*10^18:ℝ)*(4096*(3:ℝ)^(-336:ℝ)) :=
                mul_le_mul_of_nonneg_left hdecay2 (by positivity)
              have hsecondFactor :
                  γ*(D+(C:ℝ)+5)*(3:ℝ)^(2*γ*D) ≤
                    γ*A*(3:ℝ)^(2*γ*D) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDCA hγ0) (by positivity)
              calc
                _ ≤ ((1120*10^18:ℝ)*(4096*(3:ℝ)^(-336:ℝ)))*
                    (γ*(D+(C:ℝ)+5)*(3:ℝ)^(2*γ*D)) :=
                  mul_le_mul_of_nonneg_right hfirstFactor (by positivity)
                _ ≤ _ :=
                  mul_le_mul_of_nonneg_left hsecondFactor (by positivity)
            _ = _ := by ring
        calc
          _ = (7*10^18:ℝ)*p*(2*(3:ℝ)^(-(N:ℝ)))+
              (7*10^18:ℝ)*p*(80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
                ((D+(C:ℝ)+5)*(3:ℝ)^(-(N:ℝ)))) := by ring
          _ ≤ _ := add_le_add hterm0 hterm1
  have hsmall0 : (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ) ≤ 1/100 := hbaseSmall
  have hsmall1 : ((1120*10^18:ℝ)*4096)*(3:ℝ)^(-336:ℝ) ≤ 1 := horderSmall
  calc
    _ ≤ (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ)+
        ((1120*10^18:ℝ)*4096)*(3:ℝ)^(-336:ℝ)*
          (γ*A*(3:ℝ)^(2*γ*D)) := hmain
    _ ≤ 1/100+γ*A*(3:ℝ)^(2*γ*D) := by
      have htarget0 : 0 ≤ γ*A*(3:ℝ)^(2*γ*D) := by positivity
      calc
        _ ≤ 1/100+1*(γ*A*(3:ℝ)^(2*γ*D)) :=
          add_le_add hsmall0 (mul_le_mul_of_nonneg_right hsmall1 htarget0)
        _ = _ := by ring

end
end ASDExplicitGamma.Inverse
