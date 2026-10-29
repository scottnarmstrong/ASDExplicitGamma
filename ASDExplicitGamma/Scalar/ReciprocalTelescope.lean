module

public import ASDExplicitGamma.Scalar.ReciprocalIntegral
public import ASDExplicitGamma.Scalar.ReciprocalStep

/-! Discrete reciprocal drops imply the source scalar corridor by two-region integration. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory intervalIntegral

/-- Telescope the positive reciprocal intervals, retaining the endpoint order. -/
theorem sum_reciprocal_weight_intervals (S Y : ℝ) (r : ℕ → ℝ) (N : ℕ)
    (hr : ∀ i≤N,0<r i) :
    (∑ i ∈ Finset.range N, ∫ t in r (i+1)..r i,reciprocalWeight S Y t) =
      ∫ t in r N..r 0,reciprocalWeight S Y t := by
  have ht := sum_integral_adjacent_intervals (a := r) (n := N)
    (fun i hi => reciprocal_weight_intervalIntegrable S Y _ _
      (hr i hi.le) (hr (i+1) hi))
  calc
    _ = ∑ i ∈ Finset.range N, -(∫ t in r i..r (i+1),reciprocalWeight S Y t) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_symm _ _
    _ = -(∫ t in r 0..r N,reciprocalWeight S Y t) := by rw [Finset.sum_neg_distrib,ht]
    _ = _ := (integral_symm _ _).symm

/-- Finite clock increments telescope without a remainder. -/
theorem sum_clock_increments (B : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N,(B (i+1)-B i))=B N-B 0 := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

/-- The two-region reciprocal conversion, on a finite interval reindexed from zero. -/
theorem reciprocal_telescope_nat (nu K Y : ℝ) (sigma r B : ℕ → ℝ) (N : ℕ)
    (hN : 0<N) (hnu : 0<nu) (hK : 0≤K)
    (hs : ∀ i≤N,0<sigma i)
    (hB : ∀ i<N,B i≤B (i+1))
    (hdrop : ∀ i<N,K*(B (i+1)-B i)/(sigma i)^3≤r i-r (i+1))
    (hlower : ∀ i≤N,1≤sigma i*r i)
    (hupper : ∀ i<N,sigma i*r i≤Y)
    (hstart : r 0≤nu⁻¹) (hfinal : ∀ i<N,sigma i≤sigma N) :
    nu^2+2*K/(3*Y-2)*(B N-B 0)≤(sigma N)^2 := by
  have hr (i : ℕ) (hi : i≤N) : 0<r i := by
    have h := hlower i hi
    exact pos_of_mul_pos_right (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) h) (hs i hi).le
  have hstep (i : ℕ) (hi : i<N) : r (i+1)≤r i := by
    have hp : 0≤K*(B (i+1)-B i)/(sigma i)^3 := div_nonneg
      (mul_nonneg hK (sub_nonneg.mpr (hB i hi))) (pow_nonneg (hs i hi.le).le 3)
    linarith only [hp,hdrop i hi]
  have hrzero : ∀ i : ℕ, i≤N → r i≤r 0 := by
    intro i
    induction i with
    | zero => intro hi; exact le_rfl
    | succ i ih =>
      intro hi
      exact (hstep i hi).trans (ih (Nat.le_of_succ_le hi))
  have hY : 1≤Y := (hlower 0 (Nat.zero_le N)).trans (hupper 0 hN)
  have hsend : 0<sigma N := hs N le_rfl
  have ha : (sigma N)⁻¹≤r N := (inv_le_iff_one_le_mul₀ hsend).mpr (by
    simpa only [mul_comm] using hlower N le_rfl)
  have hb : r 0≤nu⁻¹ := hstart
  have hnuS : nu≤sigma N := by
    have h0 : (sigma 0)⁻¹≤nu⁻¹ :=
      ((inv_le_iff_one_le_mul₀ (hs 0 (Nat.zero_le N))).mpr (by
        simpa only [mul_comm] using hlower 0 (Nat.zero_le N))).trans hb
    exact ((inv_le_inv₀ (hs 0 (Nat.zero_le N)) hnu).mp h0).trans (hfinal 0 hN)
  have hsum : K*(B N-B 0)≤∫ t in r N..r 0,reciprocalWeight (sigma N) Y t := by
    have hp (i : ℕ) (hi : i∈Finset.range N) :
        K*(B (i+1)-B i)≤∫ t in r (i+1)..r i,reciprocalWeight (sigma N) Y t := by
      have hin := Finset.mem_range.mp hi
      exact reciprocal_drop_le_weight_integral _ _ _ _ _ _ (hs i hin.le) (hr (i+1) hin)
        (hstep i hin) (hfinal i hin) (hupper i hin)
        (by simpa only [mul_comm] using (div_le_iff₀ (pow_pos (hs i hin.le) 3)).mp (hdrop i hin))
    have h := Finset.sum_le_sum hp
    rw [sum_reciprocal_weight_intervals _ _ r N hr,← Finset.mul_sum] at h
    rwa [sum_clock_increments B N] at h
  have hi := integral_mono_interval ha (hrzero N le_rfl) hb
    (show 0 ≤ᵐ[volume.restrict (Set.Ioc (sigma N)⁻¹ nu⁻¹)] reciprocalWeight (sigma N) Y from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact reciprocal_weight_nonnegative _ _ t hsend.le (by linarith only [hY])
        ((inv_pos.mpr hsend).trans ht.1))
    (reciprocal_weight_intervalIntegrable (sigma N) Y _ _ (inv_pos.mpr hsend) (inv_pos.mpr hnu))
  have hbound := hsum.trans (hi.trans (reciprocal_integral_bound nu (sigma N) Y hnu hnuS hY))
  have hden : 0<3*Y-2 := by linarith only [hY]
  have hconvert : 2*K/(3*Y-2)*(B N-B 0)≤(sigma N)^2-nu^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hbound]
  linarith only [hconvert]

end ASDExplicitGamma.Scalar
