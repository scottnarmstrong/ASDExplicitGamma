module

public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget

/-! Constant-one complete square-norm budget for the actual OLD first
corrector estimates, preserving the affine and oscillation terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Pointwise nonnegative linear bounds pass to the complete square norm
with the same two coefficients. Convergence is proved before using tsum. -/
theorem old_signed_series_linear_budget {I : Type*} (a b g : I → ℝ) (c d : ℝ)
    (ha : ∀ n,0≤a n) (hb : ∀ n,0≤b n) (hg : ∀ n,0≤g n)
    (hc : 0≤c) (hd : 0≤d)
    (has : Summable (fun n => a n^2)) (hbs : Summable (fun n => b n^2))
    (hbound : ∀ n,g n≤c*a n+d*b n) :
    Summable (fun n => g n^2) ∧
      Real.sqrt (∑' n,g n^2)≤c*Real.sqrt (∑' n,a n^2)+d*Real.sqrt (∑' n,b n^2) := by
  have hm := old_signed_series_pairing_budget a b (fun n => a n*b n) ha hb has hbs
    (fun n => le_of_eq (abs_of_nonneg (mul_nonneg (ha n) (hb n))))
  have hsum := ((has.mul_left (c^2)).add (hm.1.mul_left (2*c*d))).add (hbs.mul_left (d^2))
  have hlinear : Summable (fun n => (c*a n+d*b n)^2) := hsum.congr (fun n => by ring)
  have hpoint (n : I) : g n^2≤(c*a n+d*b n)^2 := pow_le_pow_left₀ (hg n) (hbound n) 2
  have hgs := hlinear.of_nonneg_of_le (fun n => sq_nonneg _) hpoint
  refine ⟨hgs,Real.sqrt_le_iff.mpr ⟨add_nonneg
    (mul_nonneg hc (Real.sqrt_nonneg _)) (mul_nonneg hd (Real.sqrt_nonneg _)),?_⟩⟩
  have ht := hgs.tsum_le_tsum hpoint hlinear
  have hidentity : (∑' n,(c*a n+d*b n)^2)=
      c^2*(∑' n,a n^2)+2*c*d*(∑' n,a n*b n)+d^2*(∑' n,b n^2) := by
    calc
      _ = ∑' n,((c^2*a n^2+2*c*d*(a n*b n))+d^2*b n^2) := tsum_congr (fun n => by ring)
      _ = _ := by
        rw [Summable.tsum_add ((has.mul_left (c^2)).add (hm.1.mul_left (2*c*d)))
          (hbs.mul_left (d^2)),Summable.tsum_add (has.mul_left (c^2)) (hm.1.mul_left (2*c*d)),
          tsum_mul_left,tsum_mul_left,tsum_mul_left]
  rw [hidentity] at ht
  have hmix := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hm.2)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hc) hd)
  have hsa : Real.sqrt (∑' n,a n^2)^2=∑' n,a n^2 :=
    Real.sq_sqrt (tsum_nonneg (fun n => sq_nonneg (a n)))
  have hsb : Real.sqrt (∑' n,b n^2)^2=∑' n,b n^2 :=
    Real.sq_sqrt (tsum_nonneg (fun n => sq_nonneg (b n)))
  calc
    _ ≤ c^2*(∑' n,a n^2)+2*c*d*(∑' n,a n*b n)+d^2*(∑' n,b n^2) := ht
    _ ≤ c^2*(∑' n,a n^2)+2*c*d*(Real.sqrt (∑' n,a n^2)*Real.sqrt (∑' n,b n^2))+
        d^2*(∑' n,b n^2) := add_le_add (add_le_add le_rfl hmix) le_rfl
    _ = c^2*Real.sqrt (∑' n,a n^2)^2+
        2*c*d*(Real.sqrt (∑' n,a n^2)*Real.sqrt (∑' n,b n^2))+
        d^2*Real.sqrt (∑' n,b n^2)^2 := by rw [hsa,hsb]
    _ = _ := by ring

/-- The same constant-one linear square budget, with all finite loads
inside the complete mode sum. -/
theorem old_signed_load_series_linear_budget {I A : Type*} [Fintype A]
    (a b g : I → A → ℝ) (c d : ℝ)
    (ha : ∀ n i,0≤a n i) (hb : ∀ n i,0≤b n i) (hg : ∀ n i,0≤g n i)
    (hc : 0≤c) (hd : 0≤d)
    (has : Summable (fun n => ∑ i,a n i^2))
    (hbs : Summable (fun n => ∑ i,b n i^2))
    (hbound : ∀ n i,g n i≤c*a n i+d*b n i) :
    Summable (fun n => ∑ i,g n i^2) ∧
      Real.sqrt (∑' n,∑ i,g n i^2)≤
        c*Real.sqrt (∑' n,∑ i,a n i^2)+d*Real.sqrt (∑' n,∑ i,b n i^2) := by
  have has' : Summable (fun p : I × A => a p.1 p.2^2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
      ⟨fun _ => Summable.of_finite,by simpa only [tsum_fintype] using has⟩
  have hbs' : Summable (fun p : I × A => b p.1 p.2^2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
      ⟨fun _ => Summable.of_finite,by simpa only [tsum_fintype] using hbs⟩
  have hh := old_signed_series_linear_budget (fun p : I × A => a p.1 p.2)
    (fun p => b p.1 p.2) (fun p => g p.1 p.2) c d
    (fun p => ha p.1 p.2) (fun p => hb p.1 p.2) (fun p => hg p.1 p.2) hc hd has' hbs'
    (fun p => hbound p.1 p.2)
  refine ⟨by simpa only [tsum_fintype] using hh.1.prod,?_⟩
  simpa only [hh.1.tsum_prod,has'.tsum_prod,hbs'.tsum_prod,tsum_fintype] using hh.2

end
end ASDExplicitGamma.Native
