module

public import ASDExplicitGamma.Inverse.AssemblyTraceProfile
public import ASDExplicitGamma.Inverse.FullResponseDecayNumerics

/-! Uniform numerical extraction for the sharp selected whole-root wave series. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

private theorem assembly_profile_tail_nonneg
    (γ p : ℝ) (H0 : ℕ) (hH0 : 333 ≤ H0) (j : Fin 2) :
    0 ≤ selectedWaveExactTail γ p H0 j := by
  have hz : 0 ≤ selectedFirstClock H0 := by
    unfold selectedFirstClock
    have hh : (333:ℝ) ≤ (H0:ℝ) := by exact_mod_cast hH0
    linarith
  unfold selectedWaveExactTail
  apply tsum_nonneg
  intro n
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hclock : 0 ≤ selectedFirstClock H0+(n:ℝ) := by linarith
  unfold selectedTailProbability
  positivity

private theorem assembly_wave_geom_profile_caps (γ : ℝ)
    (hγ : γ ≤ gammaZero) :
    assemblyWaveGeom0 γ ≤ 59/41 ∧
      assemblyWaveGeom1 γ ≤ 15/4 := by
  let q := assemblyWaveDecayRatio γ
  have hγ' : γ ≤ 17/50000 := by simpa [gammaZero] using hγ
  have hq0 : 0 < q := by dsimp [q]; exact assembly_wave_decay_ratio_pos γ
  have hq1 : q < 1 := by dsimp [q]; exact assembly_wave_decay_ratio_lt_one γ hγ
  have hqcap : q ≤ 59/100 := by
    dsimp [q,assemblyWaveDecayRatio]
    have hexp : 8*γ-1/2 ≤ -(49/100:ℝ) := by nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hexp).trans
      full_response_three_neg_49_le
  have hgap : 41/100 ≤ 1-q := by nlinarith
  have hden : 0 < 1-q := by linarith
  constructor
  · unfold assemblyWaveGeom0
    apply (div_le_iff₀ hden).2
    nlinarith [hqcap]
  · unfold assemblyWaveGeom1
    apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    nlinarith [hqcap,hgap,sq_nonneg ((1-q)-(41/100:ℝ))]

theorem assembly_selected_wave_series_normed_cap
    (γ p D : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ)
    (hp : 2 ≤ p) (hD : 0 ≤ D) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyWholeRootWaveSelectedSeriesBudget γ p D E ≤
      2600*γ*((E:ℝ)+20+p*(D+1))*
        (3:ℝ)^(4*γ*((E:ℝ)+20)+2*γ*D) := by
  let k := orderBand p
  let E := heightEntrance k
  let z := selectedFirstClock E
  let P := p*(D+1)
  let A := (E:ℝ)+20+P
  let B := (3:ℝ)^(4*γ*((E:ℝ)+20))
  let S := (3:ℝ)^(22*γ)
  let T0 := selectedWaveExactTail γ p E (0:Fin 2)
  let T1 := selectedWaveExactTail γ p E (1:Fin 2)
  let C := (12:ℝ)^(1/p:ℝ)*(3:ℝ)^(4*γ*(z+4)+2*γ)
  have hE : 333 ≤ E := by unfold E heightEntrance; omega
  have hEreal : (333:ℝ) ≤ E := by exact_mod_cast hE
  have hzE : z=(E:ℝ)-26 := by
    dsimp only [z]
    unfold selectedFirstClock
    norm_num
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hA0 : 353 ≤ A := by dsimp [A]; linarith [hEreal,hP0]
  have hApos : 0 < A := by linarith
  have hPleA : P ≤ A := by dsimp [A]; linarith [hEreal]
  have hD1 : 0 ≤ D+1 := by linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hT00 : 0 ≤ T0 := by
    dsimp only [T0]
    exact assembly_profile_tail_nonneg γ p E hE 0
  have hT10 : 0 ≤ T1 := by
    dsimp only [T1]
    exact assembly_profile_tail_nonneg γ p E hE 1
  have hT0 : S*T0 ≤ B/1000 := by
    have hh := assembly_selected_tail_normed_cap γ p hγ hγ0 hp (0:Fin 2)
    simpa [S,B,E,k] using hh
  have hT1 : S*T1 ≤ B/1000 := by
    have hh := assembly_selected_tail_normed_cap γ p hγ hγ0 hp (1:Fin 2)
    simpa [S,B,E,k] using hh
  have hinv : (1/p:ℝ) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hp
  have hrootpow : (12:ℝ)^(1/2:ℝ)=Real.sqrt 12 := by rw [Real.sqrt_eq_rpow]
  have hrootsmall : Real.sqrt 12 ≤ 7/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤12)
    nlinarith only [hs]
  have hcoeff : (12:ℝ)^(1/p:ℝ) ≤ 7/2 := by
    calc
      _ ≤ (12:ℝ)^(1/2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤12) hinv
      _ = Real.sqrt 12 := hrootpow
      _ ≤ 7/2 := hrootsmall
  have hCexp : 4*γ*(z+4)+2*γ ≤ 4*γ*((E:ℝ)+20) := by
    rw [hzE]
    nlinarith [hγ0]
  have hCpow : (3:ℝ)^(4*γ*(z+4)+2*γ) ≤ B := by
    dsimp [B]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hCexp
  have hC : C ≤ (7/2)*B := by
    dsimp only [C]
    calc
      _ ≤ (7/2)*(3:ℝ)^(4*γ*(z+4)+2*γ) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ (7/2)*B := mul_le_mul_of_nonneg_left hCpow (by norm_num)
  have hzpoly : z+5+P ≤ A := by rw [hzE]; dsimp [A]; nlinarith [hP0]
  have hzpoly0 : 0 ≤ z+5+P := by rw [hzE]; linarith [hEreal,hP0]
  have hCandidate : C*(z+5+P) ≤ (7/2)*A*B := by
    calc
      _ ≤ ((7/2)*B)*(z+5+P) :=
        mul_le_mul_of_nonneg_right hC hzpoly0
      _ ≤ ((7/2)*B)*A := mul_le_mul_of_nonneg_left hzpoly (by positivity)
      _ = (7/2)*A*B := by ring
  have hTailCore : S*(T1+(6+2*P)*T0) ≤ (3/100)*A*B := by
    have hcoefTail : (7+2*P)/1000 ≤ (3/100)*A := by
      have hPbound : 7+2*P ≤ 3*A := by nlinarith [hA0,hPleA]
      nlinarith
    calc
      _ = S*T1+(6+2*P)*(S*T0) := by ring
      _ ≤ B/1000+(6+2*P)*(B/1000) := by
        exact add_le_add hT1 (mul_le_mul_of_nonneg_left hT0 (by positivity))
      _ = ((7+2*P)/1000)*B := by ring
      _ ≤ (3/100)*A*B :=
        mul_le_mul_of_nonneg_right hcoefTail hB0
  have hSecondCore : 2*C+2*S*T0 ≤ (3/100)*A*B := by
    have hcoefSecond : 7+1/500 ≤ (3/100)*A := by nlinarith [hA0]
    calc
      _ ≤ 7*B+(1/500)*B := by
        apply add_le_add (by linarith only [hC])
        calc
          2*S*T0 = 2*(S*T0) := by ring
          _ ≤ 2*(B/1000) := mul_le_mul_of_nonneg_left hT0 (by norm_num)
          _ = (1/500)*B := by ring
      _ = (7+1/500)*B := by ring
      _ ≤ (3/100)*A*B :=
        mul_le_mul_of_nonneg_right hcoefSecond hB0
  have hGeom := assembly_wave_geom_profile_caps γ hγ
  have hseries0 : 0 ≤ assemblyWaveGeom0 γ := by
    unfold assemblyWaveGeom0
    exact div_nonneg (assembly_wave_decay_ratio_pos γ).le
      (sub_nonneg.mpr (assembly_wave_decay_ratio_lt_one γ hγ).le)
  have hseries1 : 0 ≤ assemblyWaveGeom1 γ := by
    unfold assemblyWaveGeom1
    exact div_nonneg (assembly_wave_decay_ratio_pos γ).le (sq_nonneg _)
  have hinner :
      (C*(z+5+P)+S*(T1+(6+2*P)*T0))*assemblyWaveGeom0 γ+
        (2*C+2*S*T0)*assemblyWaveGeom1 γ ≤
      (65/12)*A*B := by
    have hfirst := add_le_add hCandidate hTailCore
    have hfirst' : C*(z+5+P)+S*(T1+(6+2*P)*T0) ≤
        (7/2+3/100)*A*B := by nlinarith [hfirst]
    calc
      _ ≤ ((7/2+3/100)*A*B)*(59/41)+((3/100)*A*B)*(15/4) := by
        apply add_le_add
        · exact mul_le_mul hfirst' hGeom.1 hseries0 (by positivity)
        · exact mul_le_mul hSecondCore hGeom.2 hseries1 (by positivity)
      _ ≤ (65/12)*A*B := by
        have hn : ((7/2:ℝ)+3/100)*(59/41)+(3/100)*(15/4) ≤ 65/12 := by norm_num
        have hab : 0 ≤ A*B := mul_nonneg hApos.le hB0
        calc
          _ = (((7/2:ℝ)+3/100)*(59/41)+(3/100)*(15/4))*(A*B) := by ring
          _ ≤ (65/12)*(A*B) := mul_le_mul_of_nonneg_right hn hab
          _ = (65/12)*A*B := by ring
  have hrepr : assemblyWholeRootWaveSelectedSeriesBudget γ p D E =
      480*γ*(3:ℝ)^(2*γ*D)*
        ((C*(z+5+P)+S*(T1+(6+2*P)*T0))*assemblyWaveGeom0 γ+
          (2*C+2*S*T0)*assemblyWaveGeom1 γ) := by
    unfold assemblyWholeRootWaveSelectedSeriesBudget
    dsimp [z,C,S,T0,T1,P]
    ring
  have hscale : B*(3:ℝ)^(2*γ*D)=
      (3:ℝ)^(4*γ*((E:ℝ)+20)+2*γ*D) := by
    dsimp [B]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  change assemblyWholeRootWaveSelectedSeriesBudget γ p D E ≤
    2600*γ*A*(3:ℝ)^(4*γ*((E:ℝ)+20)+2*γ*D)
  calc
    _ = 480*γ*(3:ℝ)^(2*γ*D)*
        ((C*(z+5+P)+S*(T1+(6+2*P)*T0))*assemblyWaveGeom0 γ+
          (2*C+2*S*T0)*assemblyWaveGeom1 γ) := hrepr
    _ ≤ 480*γ*(3:ℝ)^(2*γ*D)*((65/12)*A*B) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 2600*γ*A*(3:ℝ)^(4*γ*((E:ℝ)+20)+2*γ*D) := by rw [← hscale]; ring

end
end ASDExplicitGamma.Inverse
