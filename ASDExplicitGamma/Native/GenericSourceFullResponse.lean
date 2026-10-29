module

public import ASDExplicitGamma.Native.GenericSourceMeans
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! Source-side degree bookkeeping for the exact full-response input.
The bank proves a p=128 bound with a true `3^t` profile; the source recurrence uses the
finite rational `E(t)` profile, so this module records the finite-domain
conversion explicitly before feeding it to the generic source recurrence. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory
open scoped ENNReal

/-- The generic source's p=128 full-response coefficient `f_h`,
with the finite rational majorant `E((2h+4)γ)`. -/
noncomputable def nativeSourceGenericFullResponseCap (gamma : ℝ) (h : ℕ) : ℝ :=
  4 * ((1009309 : ℝ) / 500000 + gamma *
    ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
      nativeSourceE gamma (h + 2)

/-- The exact p=128 full-response bank profile dominates the finite rational
profile on the source prefix `h≤1332`.  Here `E((2h+4)γ)` is represented by
`nativeSourceE γ (h+2)`. -/
theorem native_source_generic_full_response_cap_le_bank
    (gamma : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    nativeSourceFullResponseCap gamma h ≤
      nativeSourceGenericFullResponseCap gamma h := by
  let t : ℝ := (2 * (h : ℝ) + 4) * gamma
  have hhR : (h : ℝ) ≤ 1332 := by exact_mod_cast hh
  have hcoef : 2 * (h : ℝ) + 4 ≤ 2 * 1332 + 4 := by linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (by positivity) hgamma
  have htBound : t ≤ (2 * 1332 + 4) * (17 / 50000 : ℝ) := by
    dsimp [t]
    calc
      (2 * (h : ℝ) + 4) * gamma ≤ (2 * 1332 + 4) * gamma :=
        mul_le_mul_of_nonneg_right hcoef hgamma
      _ ≤ (2 * 1332 + 4) * (17 / 50000 : ℝ) :=
        mul_le_mul_of_nonneg_left hgamma0 (by norm_num)
  have htDomain : (11 / 10 : ℝ) * t < 1 := by
    have hendpoint : (11 / 10 : ℝ) *
        ((2 * 1332 + 4) * (17 / 50000 : ℝ)) < 1 := by norm_num
    nlinarith
  have hpower := Numerics.Inverse.inv_three_power_bound t ht htDomain
  have hpower' : (3 : ℝ) ^ t ≤ (1 - (11 / 10 : ℝ) * t)⁻¹ := by
    simpa only [one_div] using hpower
  have harg : 2 * ((h + 2 : ℕ) : ℝ) * gamma = t := by
    dsimp [t]
    push_cast
    ring
  have hbankEq : nativeSourceFullResponseCap gamma h =
      4 * ((1009309 : ℝ) / 500000 + gamma *
        ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) * (3 : ℝ) ^ t := by
    unfold nativeSourceFullResponseCap Inverse.rawTraceFullResponseCap
    rfl
  have hsourceEq : nativeSourceGenericFullResponseCap gamma h =
      4 * ((1009309 : ℝ) / 500000 + gamma *
        ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
        (1 - (11 / 10 : ℝ) * t)⁻¹ := by
    unfold nativeSourceGenericFullResponseCap nativeSourceE
    rw [harg]
  have hcoefNonneg : 0 ≤ 4 * ((1009309 : ℝ) / 500000 + gamma *
      ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) := by
    have hheight : 0 ≤ (32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216 := by
      positivity
    positivity
  rw [hbankEq, hsourceEq]
  exact mul_le_mul_of_nonneg_left hpower' hcoefNonneg

/-- The exact shell variance coefficient has degree one on the finite
rational domain. -/
noncomputable def nativeSourceGenericVarianceCap (gamma : ℝ) (h : ℕ) : ℝ :=
  (9 / 2 : ℝ) * gamma * nativeSourceE gamma h

theorem native_source_generic_variance_cap_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1334) :
    nativeSourceGenericVarianceCap gamma h ≤
      theta * nativeSourceGenericVarianceCap (17 / 50000) h := by
  have htheta : 0 ≤ theta := by
    rw [hthetaEq]
    positivity
  have hgammaScaled : gamma = theta * (17 / 50000 : ℝ) := by
    rw [hthetaEq]
    field_simp
  have hE := native_source_E_le_endpoint gamma h hgamma hgamma0 hh
  unfold nativeSourceGenericVarianceCap
  calc
    (9 / 2 : ℝ) * gamma * nativeSourceE gamma h =
        (9 / 2 : ℝ) * (theta * (17 / 50000 : ℝ)) * nativeSourceE gamma h := by
          rw [hgammaScaled]
    _ =
        theta * ((9 / 2 : ℝ) * (17 / 50000 : ℝ) * nativeSourceE gamma h) := by ring
    _ ≤ theta * ((9 / 2 : ℝ) * (17 / 50000 : ℝ) *
          nativeSourceE (17 / 50000) h) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE (by norm_num)) htheta
    _ = theta * ((9 / 2 : ℝ) * (17 / 50000 : ℝ) *
          nativeSourceE (17 / 50000) h) := by ring

/-- The exact p=128 response coefficient is positive on the finite prefix. -/
theorem native_source_generic_full_response_cap_nonneg
    (gamma : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    0 ≤ nativeSourceGenericFullResponseCap gamma h := by
  have hE := native_source_E_nonneg gamma (h + 2) hgamma hgamma0 (by omega)
  unfold nativeSourceGenericFullResponseCap
  positivity

/-- The exact p=128 response coefficient has degree zero on the finite
prefix: only the shell variance carries one power of `γ`. -/
theorem native_source_generic_full_response_cap_degree
    (gamma : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    nativeSourceGenericFullResponseCap gamma h ≤
      nativeSourceGenericFullResponseCap (17 / 50000) h := by
  have hE := native_source_E_le_endpoint gamma (h + 2)
    hgamma hgamma0 (by omega)
  have hEpos := native_source_E_nonneg gamma (h + 2)
    hgamma hgamma0 (by omega)
  have hE0 := native_source_E_nonneg (17 / 50000) (h + 2)
    (by norm_num) (by norm_num) (by omega)
  have hcoef : 0 ≤ (32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216 := by
    positivity
  have hlin : 1009309 / 500000 + gamma *
        ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216) ≤
      1009309 / 500000 + (17 / 50000 : ℝ) *
        ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216) := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hgamma0 hcoef)
  calc
    _ = 4 * (1009309 / 500000 + gamma *
        ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
        nativeSourceE gamma (h + 2) := by rfl
    _ ≤ 4 * (1009309 / 500000 + (17 / 50000 : ℝ) *
        ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
        nativeSourceE (17 / 50000) (h + 2) := by
          calc
            _ ≤ 4 * (1009309 / 500000 + (17 / 50000 : ℝ) *
                ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
                nativeSourceE gamma (h + 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlin (by norm_num)) hEpos
            _ ≤ 4 * (1009309 / 500000 + (17 / 50000 : ℝ) *
                ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
                nativeSourceE (17 / 50000) (h + 2) := by
              exact mul_le_mul_of_nonneg_left hE
                (by positivity)
    _ = nativeSourceGenericFullResponseCap (17 / 50000) h := by rfl

/-- The averaging multiplier `1+50·11/3^9` used by the source state engine. -/
noncomputable def nativeSourceAverageFactor : ℝ := 1 + 550 / (3 : ℝ) ^ 9

/-- The unrefined p=20 increment obtained from the exact finite
variance and full-response profiles. -/
noncomputable def nativeSourceGenericRawIncrement (gamma : ℝ) (h : ℕ) : ℝ :=
  nativeSourceRawMomentIncrement h (nativeSourceGenericVarianceCap gamma h)
    (nativeSourceGenericFullResponseCap gamma h)

/-- The raw source scalar cap before its four individual-cap refinements. -/
noncomputable def nativeSourceGenericRawFrameInput
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) +
    nativeSourceGenericRawIncrement gamma h

/-- The finite-domain raw-frame profile from the exact source formula. -/
noncomputable def nativeSourceGenericRawFrame
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  nativeSourceWeakFrame gamma h (nativeSourceGenericRawFrameInput gamma theta h)

/-- The exact four-pass individual p=20 cap used by the finite generic source
producer. -/
noncomputable def nativeSourceGenericIndividualProfile
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  nativeSourceGenericIndividualCap h ((3 / 50 : ℝ) * theta)
    (nativeSourceGenericVarianceCap gamma h)
    (nativeSourceGenericFullResponseCap gamma h) 4

/-- The complete generic source mean profile: the scalar formula through the
finite cut `160`, followed by the raw-frame profile for every later depth. -/
noncomputable def nativeSourceGenericMeanProfile
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  if h ≤ 160 then
    nativeSourceGenericMean gamma h ((3 / 50 : ℝ) * theta)
      (3 / 10 ^ 46 : ℝ) (nativeSourceGenericIndividualProfile gamma theta h)
      (nativeSourceGenericVarianceCap gamma h)
  else
    nativeSourceGenericRawFrame gamma theta h

/-- The weak-inverse source profile uses the refined four-pass frame through
depth `160` and the raw frame afterwards. -/
noncomputable def nativeSourceGenericWeakFrameProfile
    (gamma theta : ℝ) (h : ℕ) : ℝ :=
  if h ≤ 160 then
    nativeSourceWeakFrame gamma h (nativeSourceGenericIndividualProfile gamma theta h)
  else
    nativeSourceGenericRawFrame gamma theta h

/-- The raw unrefined moment increment in (10) is nonnegative on the finite
source prefix. -/
theorem native_source_generic_raw_increment_nonneg
    (gamma : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    0 ≤ nativeSourceGenericRawIncrement gamma h := by
  have he : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    positivity
  have hf := native_source_generic_full_response_cap_nonneg gamma h hgamma hgamma0 hh
  unfold nativeSourceGenericRawIncrement
  unfold nativeSourceRawMomentIncrement
  have hA : 0 ≤ (78 * (h : ℝ) + 76 * nativeSourceK) * nativeSourceB128 := by
    apply mul_nonneg
    · exact add_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (by norm_num [nativeSourceK])
    · norm_num [nativeSourceB128]
  have hB : 0 ≤ 2 * nativeSourceK * nativeSourceB128 := by
    norm_num [nativeSourceK, nativeSourceB128]
  have hC : 0 ≤ (nativeSourceM + 38 * nativeSourceQ) * nativeSourceB128 ^ 2 := by
    norm_num [nativeSourceM, nativeSourceQ, nativeSourceB128]
  positivity

/-- The unrefined raw-frame input has degree one, combining its averaged
initial mean and the exact unrefined source increment. -/
theorem native_source_generic_raw_frame_input_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericRawFrameInput gamma theta h ≤
      theta * nativeSourceGenericRawFrameInput (17 / 50000) 1 h := by
  have htheta : 0 ≤ theta := by
    rw [hthetaEq]
    exact div_nonneg hgamma (by norm_num)
  have htheta1 : theta ≤ 1 := by
    rw [hthetaEq]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 17 / 50000)).2
    simpa only [one_mul] using hgamma0
  have ha : 0 ≤ (3 / 50 : ℝ) * theta := mul_nonneg (by norm_num) htheta
  have ha0 : 0 ≤ (3 / 50 : ℝ) := by norm_num
  have hacap : (3 / 50 : ℝ) * theta ≤ theta * (3 / 50 : ℝ) :=
    le_of_eq (by ring)
  have he : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    positivity
  have he0 : 0 ≤ nativeSourceGenericVarianceCap (17 / 50000) h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg (17 / 50000) h
      (by norm_num) (by norm_num) (by omega)
    positivity
  have hecap := native_source_generic_variance_cap_degree
    gamma theta h hgamma hgamma0 hthetaEq (by omega)
  have hf := native_source_generic_full_response_cap_nonneg
    gamma h hgamma hgamma0 hh
  have hf0 := native_source_generic_full_response_cap_nonneg
    (17 / 50000) h (by norm_num) (by norm_num) hh
  have hfcap := native_source_generic_full_response_cap_degree
    gamma h hgamma hgamma0 hh
  have hpass := native_source_generic_pass_degree_split h htheta htheta1
    ha ha0 hacap he he0 hecap hf hf0 hfcap 0
  have hincrement : nativeSourceGenericRawIncrement gamma h ≤
      theta * nativeSourceGenericRawIncrement (17 / 50000) h := by
    simpa [nativeSourceGenericRawIncrement, nativeSourceGenericPassCap] using hpass
  have hmean : nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) =
      theta * (nativeSourceAverageFactor * (3 / 50 : ℝ)) := by ring
  unfold nativeSourceGenericRawFrameInput
  calc
    _ = nativeSourceAverageFactor * ((3 / 50 : ℝ) * theta) +
        nativeSourceGenericRawIncrement gamma h := rfl
    _ ≤ theta * (nativeSourceAverageFactor * (3 / 50 : ℝ)) +
        theta * nativeSourceGenericRawIncrement (17 / 50000) h :=
      add_le_add (le_of_eq hmean) hincrement
    _ = theta * nativeSourceGenericRawFrameInput (17 / 50000) 1 h := by
      unfold nativeSourceGenericRawFrameInput
      norm_num only [mul_one]
      ring

/-- The exact finite-domain generic raw-frame profile has degree one. -/
theorem native_source_generic_raw_frame_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericRawFrame gamma theta h ≤
      theta * nativeSourceGenericRawFrame (17 / 50000) 1 h := by
  have hinput := native_source_generic_raw_frame_input_degree
    gamma theta h hgamma hgamma0 hthetaEq hh
  have hinputNonneg : 0 ≤ nativeSourceGenericRawFrameInput gamma theta h := by
    unfold nativeSourceGenericRawFrameInput
    have htheta : 0 ≤ theta := by
      rw [hthetaEq]
      exact div_nonneg hgamma (by norm_num)
    have ha : 0 ≤ (3 / 50 : ℝ) * theta :=
      mul_nonneg (by norm_num) htheta
    have havg : 0 ≤ nativeSourceAverageFactor := by
      norm_num [nativeSourceAverageFactor]
    exact add_nonneg (mul_nonneg havg ha)
      (native_source_generic_raw_increment_nonneg gamma h hgamma hgamma0 hh)
  have hframe := native_source_weak_frame_degree gamma theta
    (nativeSourceGenericRawFrameInput gamma theta h)
    (nativeSourceGenericRawFrameInput (17 / 50000) 1 h) h
    hgamma hgamma0 hthetaEq hinputNonneg hinput (by omega)
  exact hframe

/-- Nonnegativity of the exact finite-domain generic raw-frame profile. -/
theorem native_source_generic_raw_frame_nonneg
    (gamma theta : ℝ) (h : ℕ) (hgamma : 0 ≤ gamma) (htheta : 0 ≤ theta)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    0 ≤ nativeSourceGenericRawFrame gamma theta h := by
  have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
  have hinputNonneg : 0 ≤ nativeSourceGenericRawFrameInput gamma theta h := by
    unfold nativeSourceGenericRawFrameInput
    have ha : 0 ≤ (3 / 50 : ℝ) * theta :=
      mul_nonneg (by norm_num) htheta
    have havg : 0 ≤ nativeSourceAverageFactor := by
      norm_num [nativeSourceAverageFactor]
    exact add_nonneg (mul_nonneg havg ha)
      (native_source_generic_raw_increment_nonneg gamma h hgamma hgamma0 hh)
  unfold nativeSourceGenericRawFrame nativeSourceWeakFrame
  have hlinear : 0 ≤ 1 + nativeSourceFrameEta := by
    norm_num [nativeSourceFrameEta]
  have hquad : 0 ≤ 8 * (1 + 1 / nativeSourceFrameEta) := by
    norm_num [nativeSourceFrameEta]
  exact mul_nonneg hE (add_nonneg
    (mul_nonneg hlinear hinputNonneg)
    (mul_nonneg hquad (sq_nonneg _)))

/-- The exact four-pass individual p=20 source cap has degree one after
instantiating the shell variance and p=128 response profiles. -/
theorem native_source_generic_individual_four_pass_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericIndividualCap h
        ((3 / 50 : ℝ) * theta)
        (nativeSourceGenericVarianceCap gamma h)
        (nativeSourceGenericFullResponseCap gamma h) 4 ≤
      theta * nativeSourceGenericIndividualCap h (3 / 50 : ℝ)
        (nativeSourceGenericVarianceCap (17 / 50000) h)
        (nativeSourceGenericFullResponseCap (17 / 50000) h) 4 := by
  have htheta : 0 ≤ theta := by
    rw [hthetaEq]
    exact div_nonneg hgamma (by norm_num)
  have htheta1 : theta ≤ 1 := by
    rw [hthetaEq]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 17 / 50000)).2
    simpa only [one_mul] using hgamma0
  have ha : 0 ≤ (3 / 50 : ℝ) * theta := mul_nonneg (by norm_num) htheta
  have ha0 : 0 ≤ (3 / 50 : ℝ) := by norm_num
  have hacap : (3 / 50 : ℝ) * theta ≤ theta * (3 / 50 : ℝ) :=
    le_of_eq (by ring)
  have he : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    positivity
  have he0 : 0 ≤ nativeSourceGenericVarianceCap (17 / 50000) h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg (17 / 50000) h
      (by norm_num) (by norm_num) (by omega)
    positivity
  have hecap := native_source_generic_variance_cap_degree
    gamma theta h hgamma hgamma0 hthetaEq (by omega)
  have hf := native_source_generic_full_response_cap_nonneg
    gamma h hgamma hgamma0 hh
  have hf0 := native_source_generic_full_response_cap_nonneg
    (17 / 50000) h (by norm_num) (by norm_num) hh
  have hfcap := native_source_generic_full_response_cap_degree
    gamma h hgamma hgamma0 hh
  exact native_source_generic_individual_degree_split h htheta htheta1
    ha ha0 hacap he he0 hecap hf hf0 hfcap 4

/-- The exact generic scalar mean, evaluated at the four-pass source cap,
has degree one on the same finite prefix. -/
theorem native_source_generic_mean_four_pass_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericMean gamma h ((3 / 50 : ℝ) * theta)
        (3 / 10 ^ 46 : ℝ)
        (nativeSourceGenericIndividualCap h
          ((3 / 50 : ℝ) * theta)
          (nativeSourceGenericVarianceCap gamma h)
          (nativeSourceGenericFullResponseCap gamma h) 4)
        (nativeSourceGenericVarianceCap gamma h) ≤
      theta * nativeSourceGenericMean (17 / 50000) h (3 / 50 : ℝ)
        (3 / 10 ^ 46 : ℝ)
        (nativeSourceGenericIndividualCap h (3 / 50 : ℝ)
          (nativeSourceGenericVarianceCap (17 / 50000) h)
          (nativeSourceGenericFullResponseCap (17 / 50000) h) 4)
        (nativeSourceGenericVarianceCap (17 / 50000) h) := by
  have htheta : 0 ≤ theta := by
    rw [hthetaEq]
    exact div_nonneg hgamma (by norm_num)
  have htheta1 : theta ≤ 1 := by
    rw [hthetaEq]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 17 / 50000)).2
    simpa only [one_mul] using hgamma0
  have ha0 : 0 ≤ (3 / 50 : ℝ) := by norm_num
  have ha : 0 ≤ (3 / 50 : ℝ) * theta := mul_nonneg ha0 htheta
  have hacap : (3 / 50 : ℝ) * theta ≤ theta * (3 / 50 : ℝ) :=
    le_of_eq (by ring)
  have hx : 0 ≤ nativeSourceGenericIndividualCap h
      ((3 / 50 : ℝ) * theta)
      (nativeSourceGenericVarianceCap gamma h)
      (nativeSourceGenericFullResponseCap gamma h) 4 := by
    exact native_source_generic_individual_nonneg h
      ((3 / 50 : ℝ) * theta)
      (nativeSourceGenericVarianceCap gamma h)
      (nativeSourceGenericFullResponseCap gamma h) ha
      (by
        unfold nativeSourceGenericVarianceCap
        have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
        positivity)
      (native_source_generic_full_response_cap_nonneg gamma h hgamma hgamma0 hh) 4
  have hx0 : 0 ≤ nativeSourceGenericIndividualCap h (3 / 50 : ℝ)
      (nativeSourceGenericVarianceCap (17 / 50000) h)
      (nativeSourceGenericFullResponseCap (17 / 50000) h) 4 := by
    exact native_source_generic_individual_nonneg h (3 / 50 : ℝ)
      (nativeSourceGenericVarianceCap (17 / 50000) h)
      (nativeSourceGenericFullResponseCap (17 / 50000) h) ha0
      (by
        unfold nativeSourceGenericVarianceCap
        have hE := native_source_E_nonneg (17 / 50000) h
          (by norm_num) (by norm_num) (by omega)
        positivity)
      (native_source_generic_full_response_cap_nonneg
        (17 / 50000) h (by norm_num) (by norm_num) hh) 4
  have hxcap := native_source_generic_individual_four_pass_degree
    gamma theta h hgamma hgamma0 hthetaEq hh
  have he : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    positivity
  have he0 : 0 ≤ nativeSourceGenericVarianceCap (17 / 50000) h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg (17 / 50000) h
      (by norm_num) (by norm_num) (by omega)
    positivity
  have hecap := native_source_generic_variance_cap_degree
    gamma theta h hgamma hgamma0 hthetaEq (by omega)
  exact native_source_generic_mean_degree gamma theta
    ((3 / 50 : ℝ) * theta) (3 / 50 : ℝ) (3 / 10 ^ 46 : ℝ)
    (nativeSourceGenericIndividualCap h
      ((3 / 50 : ℝ) * theta)
      (nativeSourceGenericVarianceCap gamma h)
      (nativeSourceGenericFullResponseCap gamma h) 4)
    (nativeSourceGenericIndividualCap h (3 / 50 : ℝ)
      (nativeSourceGenericVarianceCap (17 / 50000) h)
      (nativeSourceGenericFullResponseCap (17 / 50000) h) 4)
    (nativeSourceGenericVarianceCap gamma h)
    (nativeSourceGenericVarianceCap (17 / 50000) h) h
    hgamma hgamma0 hthetaEq ha0 ha hacap he he0 hecap
    (by norm_num) hx hx0 hxcap (by omega)

/-- Degree-one comparison of the four-pass individual profile using the
source-side rational p=128 cap. -/
theorem native_source_generic_individual_profile_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericIndividualProfile gamma theta h ≤
      theta * nativeSourceGenericIndividualProfile (17 / 50000) 1 h := by
  simpa only [nativeSourceGenericIndividualProfile, mul_one] using
    (native_source_generic_individual_four_pass_degree
      gamma theta h hgamma hgamma0 hthetaEq hh)

/-- The four-pass individual source profile is nonnegative on its finite
rational domain. -/
theorem native_source_generic_individual_profile_nonneg
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (htheta : 0 ≤ theta)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    0 ≤ nativeSourceGenericIndividualProfile gamma theta h := by
  have he : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
    unfold nativeSourceGenericVarianceCap
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    positivity
  have hf := native_source_generic_full_response_cap_nonneg gamma h hgamma hgamma0 hh
  unfold nativeSourceGenericIndividualProfile
  exact native_source_generic_individual_nonneg h ((3 / 50 : ℝ) * theta)
    (nativeSourceGenericVarianceCap gamma h)
    (nativeSourceGenericFullResponseCap gamma h)
    (mul_nonneg (by norm_num) htheta) he hf 4

/-- Degree-one comparison of the exact piecewise generic source mean profile
through the complete finite prefix. -/
theorem native_source_generic_mean_profile_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericMeanProfile gamma theta h ≤
      theta * nativeSourceGenericMeanProfile (17 / 50000) 1 h := by
  classical
  unfold nativeSourceGenericMeanProfile
  split_ifs with hcut
  · simpa [nativeSourceGenericIndividualProfile, mul_one, one_mul] using
      (native_source_generic_mean_four_pass_degree
        gamma theta h hgamma hgamma0 hthetaEq (by omega))
  · exact native_source_generic_raw_frame_degree
      gamma theta h hgamma hgamma0 hthetaEq hh

/-- Nonnegativity of the exact piecewise generic source mean profile. -/
theorem native_source_generic_mean_profile_nonneg
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (htheta : 0 ≤ theta)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    0 ≤ nativeSourceGenericMeanProfile gamma theta h := by
  classical
  unfold nativeSourceGenericMeanProfile
  split_ifs with hcut
  · have hx := native_source_generic_individual_profile_nonneg
      gamma theta h hgamma htheta hgamma0 hh
    have he : 0 ≤ nativeSourceGenericVarianceCap gamma h := by
      unfold nativeSourceGenericVarianceCap
      have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
      positivity
    exact native_source_generic_mean_nonneg gamma h ((3 / 50 : ℝ) * theta)
      (3 / 10 ^ 46 : ℝ) (nativeSourceGenericIndividualProfile gamma theta h)
      (nativeSourceGenericVarianceCap gamma h) hgamma hgamma0
      (mul_nonneg (by norm_num) htheta) (by norm_num) hx he (by omega)
  · exact native_source_generic_raw_frame_nonneg
      gamma theta h hgamma htheta hgamma0 hh

/-- Degree-one comparison of the exact piecewise weak-inverse frame profile. -/
theorem native_source_generic_weak_frame_profile_degree
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hh : h ≤ 1332) :
    nativeSourceGenericWeakFrameProfile gamma theta h ≤
      theta * nativeSourceGenericWeakFrameProfile (17 / 50000) 1 h := by
  classical
  unfold nativeSourceGenericWeakFrameProfile
  split_ifs with hcut
  · have hx := native_source_generic_individual_profile_nonneg
      gamma theta h hgamma (by rw [hthetaEq]; positivity) hgamma0 hh
    have hxcap := native_source_generic_individual_profile_degree
      gamma theta h hgamma hgamma0 hthetaEq hh
    exact native_source_weak_frame_degree gamma theta
      (nativeSourceGenericIndividualProfile gamma theta h)
      (nativeSourceGenericIndividualProfile (17 / 50000) 1 h) h
      hgamma hgamma0 hthetaEq hx hxcap (by omega)
  · exact native_source_generic_raw_frame_degree
      gamma theta h hgamma hgamma0 hthetaEq hh

/-- Nonnegativity of the exact piecewise weak-inverse frame profile. -/
theorem native_source_generic_weak_frame_profile_nonneg
    (gamma theta : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (htheta : 0 ≤ theta)
    (hgamma0 : gamma ≤ 17 / 50000) (hh : h ≤ 1332) :
    0 ≤ nativeSourceGenericWeakFrameProfile gamma theta h := by
  classical
  unfold nativeSourceGenericWeakFrameProfile
  split_ifs with hcut
  · have hx := native_source_generic_individual_profile_nonneg
      gamma theta h hgamma htheta hgamma0 hh
    have hE := native_source_E_nonneg gamma h hgamma hgamma0 (by omega)
    have hlinear : 0 ≤ 1 + nativeSourceFrameEta := by
      norm_num [nativeSourceFrameEta]
    have hquad : 0 ≤ 8 * (1 + 1 / nativeSourceFrameEta) := by
      norm_num [nativeSourceFrameEta]
    unfold nativeSourceWeakFrame
    exact mul_nonneg hE (add_nonneg
      (mul_nonneg hlinear hx) (mul_nonneg hquad (sq_nonneg _)))
  · exact native_source_generic_raw_frame_nonneg
      gamma theta h hgamma htheta hgamma0 hh

end ASDExplicitGamma.Native
