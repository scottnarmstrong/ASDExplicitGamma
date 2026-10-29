module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0576Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 625).2.2,
  nativeAvg*nativeA+(nativeRaw 626).2.2,
  nativeAvg*nativeA+(nativeRaw 627).2.2,
  nativeAvg*nativeA+(nativeRaw 628).2.2,
  nativeAvg*nativeA+(nativeRaw 629).2.2,
  nativeAvg*nativeA+(nativeRaw 630).2.2,
  nativeAvg*nativeA+(nativeRaw 631).2.2,
  nativeAvg*nativeA+(nativeRaw 632).2.2,
  nativeAvg*nativeA+(nativeRaw 633).2.2,
  nativeAvg*nativeA+(nativeRaw 634).2.2,
  nativeAvg*nativeA+(nativeRaw 635).2.2,
  nativeAvg*nativeA+(nativeRaw 636).2.2,
  nativeAvg*nativeA+(nativeRaw 637).2.2,
  nativeAvg*nativeA+(nativeRaw 638).2.2,
  nativeAvg*nativeA+(nativeRaw 639).2.2,
  nativeAvg*nativeA+(nativeRaw 640).2.2,
  nativeAvg*nativeA+(nativeRaw 641).2.2,
  nativeAvg*nativeA+(nativeRaw 642).2.2,
  nativeAvg*nativeA+(nativeRaw 643).2.2,
  nativeAvg*nativeA+(nativeRaw 644).2.2,
  nativeAvg*nativeA+(nativeRaw 645).2.2,
  nativeAvg*nativeA+(nativeRaw 646).2.2,
  nativeAvg*nativeA+(nativeRaw 647).2.2,
  nativeAvg*nativeA+(nativeRaw 648).2.2,
  nativeAvg*nativeA+(nativeRaw 649).2.2,
  nativeAvg*nativeA+(nativeRaw 650).2.2,
  nativeAvg*nativeA+(nativeRaw 651).2.2,
  nativeAvg*nativeA+(nativeRaw 652).2.2,
  nativeAvg*nativeA+(nativeRaw 653).2.2,
  nativeAvg*nativeA+(nativeRaw 654).2.2,
  nativeAvg*nativeA+(nativeRaw 655).2.2,
  nativeAvg*nativeA+(nativeRaw 656).2.2
]

def nativeHistoryBuffer0576Start : ℚ × ℚ := ((59803198745587883394037968344665236371819882007316878155517/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687239351416921221298584243345779512232462610228720246971288643772793/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0576End : ℚ × ℚ := ((306579023859253780951388211910455767918388101771680393813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2928316185169821245340283157276868724225149111814986987475379002606711671238438976602492516955655141/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0576Inputs_length : nativeHistoryBuffer0576Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0576Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(625+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(625+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0576Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0576Inputs.getD i.val 0)*(nativeHistoryBuffer0576Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0576_checked : nativeHistorySteps 49 576 32 nativeHistoryBuffer0576Inputs nativeHistoryBuffer0576Start = nativeHistoryBuffer0576End := by
  decide +kernel

theorem nativeHistoryBuffer0576Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0576Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0576Weight : nativeHistoryRatio^576 ≤ nativeHistoryBuffer0576Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0576Real_bound : nativeHistoryReal 49 576 nativeHistoryBuffer0576Inputs ≤ (nativeHistoryBuffer0576End.2 : ℝ)-(nativeHistoryBuffer0576Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0576Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0576Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0576Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0576Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0576Inputs.length) := nativeHistoryBuffer0576Domains ⟨i,by simpa only [nativeHistoryBuffer0576Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0576Inputs.length) := nativeHistoryBuffer0576Roots ⟨i,by simpa only [nativeHistoryBuffer0576Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0576Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 576 nativeHistoryBuffer0576Inputs nativeHistoryBuffer0576Start ht hd hr hw
  simpa only [nativeHistoryBuffer0576Inputs_length,nativeHistoryBuffer0576_checked] using hs

end ASDExplicitGamma.Numerics.Native
