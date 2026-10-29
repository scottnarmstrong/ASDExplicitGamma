module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0608Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 657).2.2,
  nativeAvg*nativeA+(nativeRaw 658).2.2,
  nativeAvg*nativeA+(nativeRaw 659).2.2,
  nativeAvg*nativeA+(nativeRaw 660).2.2,
  nativeAvg*nativeA+(nativeRaw 661).2.2,
  nativeAvg*nativeA+(nativeRaw 662).2.2,
  nativeAvg*nativeA+(nativeRaw 663).2.2,
  nativeAvg*nativeA+(nativeRaw 664).2.2,
  nativeAvg*nativeA+(nativeRaw 665).2.2,
  nativeAvg*nativeA+(nativeRaw 666).2.2,
  nativeAvg*nativeA+(nativeRaw 667).2.2,
  nativeAvg*nativeA+(nativeRaw 668).2.2,
  nativeAvg*nativeA+(nativeRaw 669).2.2,
  nativeAvg*nativeA+(nativeRaw 670).2.2,
  nativeAvg*nativeA+(nativeRaw 671).2.2,
  nativeAvg*nativeA+(nativeRaw 672).2.2,
  nativeAvg*nativeA+(nativeRaw 673).2.2,
  nativeAvg*nativeA+(nativeRaw 674).2.2,
  nativeAvg*nativeA+(nativeRaw 675).2.2,
  nativeAvg*nativeA+(nativeRaw 676).2.2,
  nativeAvg*nativeA+(nativeRaw 677).2.2,
  nativeAvg*nativeA+(nativeRaw 678).2.2,
  nativeAvg*nativeA+(nativeRaw 679).2.2,
  nativeAvg*nativeA+(nativeRaw 680).2.2,
  nativeAvg*nativeA+(nativeRaw 681).2.2,
  nativeAvg*nativeA+(nativeRaw 682).2.2,
  nativeAvg*nativeA+(nativeRaw 683).2.2,
  nativeAvg*nativeA+(nativeRaw 684).2.2,
  nativeAvg*nativeA+(nativeRaw 685).2.2,
  nativeAvg*nativeA+(nativeRaw 686).2.2,
  nativeAvg*nativeA+(nativeRaw 687).2.2,
  nativeAvg*nativeA+(nativeRaw 688).2.2
]

def nativeHistoryBuffer0608Start : ℚ × ℚ := ((306579023859253780951388211910455767918388101771680393813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2928316185169821245340283157276868724225149111814986987475379002606711671238438976602492516955655141/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0608End : ℚ × ℚ := ((1571666730910899242945132856355081840621810440544157119/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538261942572699221559174851156342885443274119827641709700208941/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0608Inputs_length : nativeHistoryBuffer0608Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0608Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(657+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(657+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0608Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0608Inputs.getD i.val 0)*(nativeHistoryBuffer0608Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0608_checked : nativeHistorySteps 49 608 32 nativeHistoryBuffer0608Inputs nativeHistoryBuffer0608Start = nativeHistoryBuffer0608End := by
  decide +kernel

theorem nativeHistoryBuffer0608Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0608Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0608Weight : nativeHistoryRatio^608 ≤ nativeHistoryBuffer0608Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0608Real_bound : nativeHistoryReal 49 608 nativeHistoryBuffer0608Inputs ≤ (nativeHistoryBuffer0608End.2 : ℝ)-(nativeHistoryBuffer0608Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0608Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0608Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0608Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0608Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0608Inputs.length) := nativeHistoryBuffer0608Domains ⟨i,by simpa only [nativeHistoryBuffer0608Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0608Inputs.length) := nativeHistoryBuffer0608Roots ⟨i,by simpa only [nativeHistoryBuffer0608Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0608Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 608 nativeHistoryBuffer0608Inputs nativeHistoryBuffer0608Start ht hd hr hw
  simpa only [nativeHistoryBuffer0608Inputs_length,nativeHistoryBuffer0608_checked] using hs

end ASDExplicitGamma.Numerics.Native
