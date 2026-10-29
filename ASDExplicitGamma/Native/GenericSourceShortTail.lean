module

public import ASDExplicitGamma.Native.GenericSourceRawTailProfile

/-! A complete unbounded raw tail with its sharper physical ratio. This
allows a shorter auxiliary refined head while explicitly paying every tail. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The quadratic geometric series and its exact complete sum. -/
theorem native_source_quadratic_geometric_sum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q<1) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^2*q^n) ∧
      (∑' n : ℕ, ((n:ℝ)+1)^2*q^n)=(1+q)/(1-q)^3 := by
  have hnorm : ‖q‖<1 := by simpa only [Real.norm_of_nonneg hq0] using hq1
  have h0 : Summable (fun n : ℕ => q^n) := summable_geometric_of_lt_one hq0 hq1
  have h1 : Summable (fun n : ℕ => (n:ℝ)*q^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2 : Summable (fun n : ℕ => (n:ℝ)^2*q^n) := summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have heq : (fun n : ℕ => ((n:ℝ)+1)^2*q^n)=
      (fun n : ℕ => q^n+2*((n:ℝ)*q^n)+(n:ℝ)^2*q^n) := by funext n; ring
  refine ⟨by rw [heq]; exact (h0.add (h1.mul_left 2)).add h2,?_⟩
  rw [heq,(h0.add (h1.mul_left 2)).tsum_add h2,h0.tsum_add (h1.mul_left 2),tsum_mul_left,
    tsum_geometric_of_lt_one hq0 hq1,tsum_coe_mul_geometric_of_norm_lt_one hnorm,
    tsum_sq_mul_geometric_of_norm_lt_one hnorm]
  field_simp [ne_of_gt (sub_pos.mpr hq1)]
  ring

/-- The physical weighted raw growth ratio is below 3/5 on the entire
smaller-gamma ray. The original 9/10 allocation remains unchanged. -/
theorem native_source_history_weight_sharp_ratio (gamma : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) :
    nativeSourceHistoryWeight gamma*(3:ℝ)^(6*gamma) ≤ 3/5 := by
  have hweight := (native_source_history_weight_endpoint_and_ratio gamma hg0 hg).2.1
  have hpower := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ)≤6))
  have hE := native_source_E_ge_three_power (17/50000) 3 (by norm_num) (by norm_num) (by norm_num)
  have hE' : (3:ℝ)^(6*(17/50000:ℝ)) ≤ nativeSourceE (17/50000) 3 := by
    convert hE using 1; norm_num
  have hnum : nativeSourceHistoryWeight (17/50000)*nativeSourceE (17/50000) 3 ≤ (3/5:ℝ) := by
    norm_num [nativeSourceHistoryWeight,nativeSourceAlphaPlus,nativeSourceE]
  exact (mul_le_mul hweight (hpower.trans hE') (by positivity)
    (native_source_history_weight_endpoint_and_ratio (17/50000) (by norm_num) (by norm_num)).1).trans hnum

/-- Positivity of the true-power raw envelope with arbitrary nonnegative
source parameters, independently of a model instance. -/
theorem native_source_exponential_raw_nonneg (gamma theta : ℝ) (height : ℕ)
    (hg : 0 ≤ gamma) (ht : 0 ≤ theta) :
    0 ≤ nativeSourceExponentialRawFrame gamma theta height := by
  unfold nativeSourceExponentialRawFrame nativeSourceExponentialRawFrameInput
    nativeSourceExponentialRawIncrement nativeSourceExponentialVarianceCap
    nativeSourceExponentialFullResponseCap nativeSourceRawMomentIncrement
    nativeSourceAverageFactor nativeSourceK nativeSourceM nativeSourceQ nativeSourceB128 nativeSourceFrameEta
  positivity

/-- Every term after an arbitrary finite head is retained in this complete
raw-series bound. The sharp physical ratio sums to the explicit factor 25. -/
theorem native_source_short_raw_tail (gamma theta : ℝ) (H J : ℕ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) (ht : 0 ≤ theta) (hH : 1 ≤ H) :
    Summable (fun n : ℕ => nativeSourceHistoryWeight gamma^(J+n)*
      nativeSourceExponentialRawFrame gamma theta (H+J+n)) ∧
    (∑' n : ℕ, nativeSourceHistoryWeight gamma^(J+n)*
      nativeSourceExponentialRawFrame gamma theta (H+J+n)) ≤
      25*nativeSourceHistoryWeight gamma^J*nativeSourceExponentialRawFrame gamma theta (H+J) := by
  let q := nativeSourceHistoryWeight gamma
  let F := nativeSourceExponentialRawFrame gamma theta
  let A := q^J*F (H+J)
  have hq := (native_source_history_weight_endpoint_and_ratio gamma hg0 hg).1
  have hF (j) : 0 ≤ F j := native_source_exponential_raw_nonneg gamma theta j hg0 ht
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg hq J) (hF _)
  have hratio := native_source_history_weight_sharp_ratio gamma hg0 hg
  have hs := native_source_quadratic_geometric_sum (3/5:ℝ) (by norm_num) (by norm_num)
  have hbound (n : ℕ) : q^(J+n)*F (H+J+n) ≤ A*(((n:ℝ)+1)^2*(3/5:ℝ)^n) := by
    have hraw := native_source_exponential_raw_frame_growth gamma theta (H+J) n hg0 ht (by omega)
    have hp := pow_le_pow_left₀ (mul_nonneg hq (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) _)) hratio n
    have h1 := mul_le_mul_of_nonneg_left hraw (pow_nonneg hq (J+n))
    calc
      _ ≤ q^(J+n)*(F (H+J)*(((n+1:ℕ):ℝ)^2*((3:ℝ)^(6*gamma))^n)) := by
        convert h1 using 1
        ring
      _ = A*(((n:ℝ)+1)^2*(q*(3:ℝ)^(6*gamma))^n) := by
        dsimp only [A]
        rw [pow_add,mul_pow]
        push_cast
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (sq_nonneg _)) hA
  have hsA := hs.1.mul_left A
  have hsum : Summable (fun n : ℕ => q^(J+n)*F (H+J+n)) :=
    hsA.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hq _) (hF _)) hbound
  refine ⟨hsum,?_⟩
  have hh := hsum.tsum_le_tsum hbound hsA
  rw [tsum_mul_left,hs.2] at hh
  norm_num only at hh
  convert hh using 1
  dsimp only [A]
  ring

end
end ASDExplicitGamma.Native
