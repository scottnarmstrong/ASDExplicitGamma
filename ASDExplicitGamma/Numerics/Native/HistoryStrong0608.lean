module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0608Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 617).2.2,
  nativeAvg*nativeA+(nativeRaw 618).2.2,
  nativeAvg*nativeA+(nativeRaw 619).2.2,
  nativeAvg*nativeA+(nativeRaw 620).2.2,
  nativeAvg*nativeA+(nativeRaw 621).2.2,
  nativeAvg*nativeA+(nativeRaw 622).2.2,
  nativeAvg*nativeA+(nativeRaw 623).2.2,
  nativeAvg*nativeA+(nativeRaw 624).2.2,
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
  nativeAvg*nativeA+(nativeRaw 648).2.2
]

def nativeHistoryStrong0608Start : ℚ × ℚ := ((306579023859253780951388211910455767918388101771680393813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789866593257713705939433948435494178076914559160986358201994289339/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0608End : ℚ × ℚ := ((1571666730910899242945132856355081840621810440544157119/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895106537458366014260299019287726116929511670349172593119561937/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0608Inputs_length : nativeHistoryStrong0608Inputs.length = 32 := rfl

theorem nativeHistoryStrong0608Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(617+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(617+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0608Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0608Inputs.getD i.val 0)*(nativeHistoryStrong0608Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0608_checked : nativeHistorySteps 9 608 32 nativeHistoryStrong0608Inputs nativeHistoryStrong0608Start = nativeHistoryStrong0608End := by
  decide +kernel

theorem nativeHistoryStrong0608Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0608Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0608Weight : nativeHistoryRatio^608 ≤ nativeHistoryStrong0608Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0608Real_bound : nativeHistoryReal 9 608 nativeHistoryStrong0608Inputs ≤ (nativeHistoryStrong0608End.2 : ℝ)-(nativeHistoryStrong0608Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0608Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0608Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0608Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0608Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0608Inputs.length) := nativeHistoryStrong0608Domains ⟨i,by simpa only [nativeHistoryStrong0608Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0608Inputs.length) := nativeHistoryStrong0608Roots ⟨i,by simpa only [nativeHistoryStrong0608Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0608Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 608 nativeHistoryStrong0608Inputs nativeHistoryStrong0608Start ht hd hr hw
  simpa only [nativeHistoryStrong0608Inputs_length,nativeHistoryStrong0608_checked] using hs

end ASDExplicitGamma.Numerics.Native
