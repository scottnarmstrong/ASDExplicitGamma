module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0896Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 905).2.2,
  nativeAvg*nativeA+(nativeRaw 906).2.2,
  nativeAvg*nativeA+(nativeRaw 907).2.2,
  nativeAvg*nativeA+(nativeRaw 908).2.2,
  nativeAvg*nativeA+(nativeRaw 909).2.2,
  nativeAvg*nativeA+(nativeRaw 910).2.2,
  nativeAvg*nativeA+(nativeRaw 911).2.2,
  nativeAvg*nativeA+(nativeRaw 912).2.2,
  nativeAvg*nativeA+(nativeRaw 913).2.2,
  nativeAvg*nativeA+(nativeRaw 914).2.2,
  nativeAvg*nativeA+(nativeRaw 915).2.2,
  nativeAvg*nativeA+(nativeRaw 916).2.2,
  nativeAvg*nativeA+(nativeRaw 917).2.2,
  nativeAvg*nativeA+(nativeRaw 918).2.2,
  nativeAvg*nativeA+(nativeRaw 919).2.2,
  nativeAvg*nativeA+(nativeRaw 920).2.2,
  nativeAvg*nativeA+(nativeRaw 921).2.2,
  nativeAvg*nativeA+(nativeRaw 922).2.2,
  nativeAvg*nativeA+(nativeRaw 923).2.2,
  nativeAvg*nativeA+(nativeRaw 924).2.2,
  nativeAvg*nativeA+(nativeRaw 925).2.2,
  nativeAvg*nativeA+(nativeRaw 926).2.2,
  nativeAvg*nativeA+(nativeRaw 927).2.2,
  nativeAvg*nativeA+(nativeRaw 928).2.2,
  nativeAvg*nativeA+(nativeRaw 929).2.2,
  nativeAvg*nativeA+(nativeRaw 930).2.2,
  nativeAvg*nativeA+(nativeRaw 931).2.2,
  nativeAvg*nativeA+(nativeRaw 932).2.2,
  nativeAvg*nativeA+(nativeRaw 933).2.2,
  nativeAvg*nativeA+(nativeRaw 934).2.2,
  nativeAvg*nativeA+(nativeRaw 935).2.2,
  nativeAvg*nativeA+(nativeRaw 936).2.2
]

def nativeHistoryStrong0896Start : ℚ × ℚ := ((749729576913275489961321993062186813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820201002460466636252950846870595039842423586421851562558891/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0896End : ℚ × ℚ := ((960865667179053422125864697785571/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(380602506334511234302303271551583711595811232160393674661817459318050862121009716681271080737754453/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0896Inputs_length : nativeHistoryStrong0896Inputs.length = 32 := rfl

theorem nativeHistoryStrong0896Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(905+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(905+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0896Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0896Inputs.getD i.val 0)*(nativeHistoryStrong0896Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0896_checked : nativeHistorySteps 9 896 32 nativeHistoryStrong0896Inputs nativeHistoryStrong0896Start = nativeHistoryStrong0896End := by
  decide +kernel

theorem nativeHistoryStrong0896Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0896Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0896Weight : nativeHistoryRatio^896 ≤ nativeHistoryStrong0896Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0896Real_bound : nativeHistoryReal 9 896 nativeHistoryStrong0896Inputs ≤ (nativeHistoryStrong0896End.2 : ℝ)-(nativeHistoryStrong0896Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0896Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0896Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0896Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0896Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0896Inputs.length) := nativeHistoryStrong0896Domains ⟨i,by simpa only [nativeHistoryStrong0896Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0896Inputs.length) := nativeHistoryStrong0896Roots ⟨i,by simpa only [nativeHistoryStrong0896Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0896Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 896 nativeHistoryStrong0896Inputs nativeHistoryStrong0896Start ht hd hr hw
  simpa only [nativeHistoryStrong0896Inputs_length,nativeHistoryStrong0896_checked] using hs

end ASDExplicitGamma.Numerics.Native
