module

public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget

/-! Joint complete-mode Cauchy budgets with the finite physical loads
kept inside each mode. No independence or separate expectations are used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Joint finite-load and complete-mode pairing bound with constant one. -/
theorem old_signed_load_series_pairing_budget {I A : Type*} [Fintype A]
    (a b f : I → A → ℝ)
    (ha : ∀ n i,0≤a n i) (hb : ∀ n i,0≤b n i)
    (has : Summable (fun n => ∑ i,a n i^2))
    (hbs : Summable (fun n => ∑ i,b n i^2))
    (hbound : ∀ n i,|f n i|≤a n i*b n i) :
    Summable (fun n => ∑ i,f n i) ∧
      |∑' n,∑ i,f n i|≤Real.sqrt (∑' n,∑ i,a n i^2)*Real.sqrt (∑' n,∑ i,b n i^2) := by
  have hna (n : I) : 0≤∑ i,a n i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnb (n : I) : 0≤∑ i,b n i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsa : Summable (fun n => Real.sqrt (∑ i,a n i^2)^2) := by
    simpa only [Real.sq_sqrt (hna _)] using has
  have hsb : Summable (fun n => Real.sqrt (∑ i,b n i^2)^2) := by
    simpa only [Real.sq_sqrt (hnb _)] using hbs
  have hh := old_signed_series_pairing_budget
    (fun n => Real.sqrt (∑ i,a n i^2)) (fun n => Real.sqrt (∑ i,b n i^2))
    (fun n => ∑ i,f n i) (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) hsa hsb
    (fun n => by
      calc
        |∑ i,f n i|≤∑ i,|f n i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i,a n i*b n i := Finset.sum_le_sum (fun i _ => hbound n i)
        _ ≤ Real.sqrt (∑ i,a n i^2)*Real.sqrt (∑ i,b n i^2) := by
          have hc := Real.sum_sqrt_mul_sqrt_le Finset.univ
            (fun i => sq_nonneg (a n i)) (fun i => sq_nonneg (b n i))
          simpa only [Real.sqrt_sq (ha _ _),Real.sqrt_sq (hb _ _)] using hc)
  simpa only [Real.sq_sqrt (hna _),Real.sq_sqrt (hnb _)] using hh

/-- A signed affine baseline and joint mixed budget control a genuine
nonnegative complete energy series. The affine baseline keeps its sign. -/
theorem old_signed_load_series_energy_budget {I A : Type*} [Fintype A]
    (e c : I → ℝ) (a b : I → A → ℝ) (K M : ℝ)
    (he : ∀ n,0≤e n) (ha : ∀ n i,0≤a n i) (hb : ∀ n i,0≤b n i)
    (hK : 0≤K) (hcs : Summable c)
    (has : Summable (fun n => ∑ i,a n i^2))
    (hbs : Summable (fun n => ∑ i,b n i^2))
    (hbound : ∀ n,e n≤c n+K*(∑ i,a n i*b n i)+M*(∑ i,b n i^2)) :
    Summable e ∧ (∑' n,e n)≤(∑' n,c n)+
      K*(Real.sqrt (∑' n,∑ i,a n i^2)*Real.sqrt (∑' n,∑ i,b n i^2))+
      M*(∑' n,∑ i,b n i^2) := by
  have hm := old_signed_load_series_pairing_budget a b (fun n i => a n i*b n i)
    ha hb has hbs (fun n i => le_of_eq (abs_of_nonneg (mul_nonneg (ha n i) (hb n i))))
  have hs := (hcs.abs.add (hm.1.mul_left K)).add (hbs.mul_left M)
  have hes : Summable e := hs.of_nonneg_of_le he (fun n =>
    (hbound n).trans (add_le_add (add_le_add (le_abs_self _) le_rfl) le_rfl))
  refine ⟨hes,?_⟩
  have ht := hes.tsum_le_tsum hbound ((hcs.add (hm.1.mul_left K)).add (hbs.mul_left M))
  rw [Summable.tsum_add (hcs.add (hm.1.mul_left K)) (hbs.mul_left M),
    Summable.tsum_add hcs (hm.1.mul_left K),tsum_mul_left,tsum_mul_left] at ht
  exact ht.trans (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hm.2) hK)) le_rfl)

end
end ASDExplicitGamma.Native
