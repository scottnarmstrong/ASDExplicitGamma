module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0928Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 937).2.2,
  nativeAvg*nativeA+(nativeRaw 938).2.2,
  nativeAvg*nativeA+(nativeRaw 939).2.2,
  nativeAvg*nativeA+(nativeRaw 940).2.2,
  nativeAvg*nativeA+(nativeRaw 941).2.2,
  nativeAvg*nativeA+(nativeRaw 942).2.2,
  nativeAvg*nativeA+(nativeRaw 943).2.2,
  nativeAvg*nativeA+(nativeRaw 944).2.2,
  nativeAvg*nativeA+(nativeRaw 945).2.2,
  nativeAvg*nativeA+(nativeRaw 946).2.2,
  nativeAvg*nativeA+(nativeRaw 947).2.2,
  nativeAvg*nativeA+(nativeRaw 948).2.2,
  nativeAvg*nativeA+(nativeRaw 949).2.2,
  nativeAvg*nativeA+(nativeRaw 950).2.2,
  nativeAvg*nativeA+(nativeRaw 951).2.2,
  nativeAvg*nativeA+(nativeRaw 952).2.2,
  nativeAvg*nativeA+(nativeRaw 953).2.2,
  nativeAvg*nativeA+(nativeRaw 954).2.2,
  nativeAvg*nativeA+(nativeRaw 955).2.2,
  nativeAvg*nativeA+(nativeRaw 956).2.2,
  nativeAvg*nativeA+(nativeRaw 957).2.2,
  nativeAvg*nativeA+(nativeRaw 958).2.2,
  nativeAvg*nativeA+(nativeRaw 959).2.2,
  nativeAvg*nativeA+(nativeRaw 960).2.2,
  nativeAvg*nativeA+(nativeRaw 961).2.2,
  nativeAvg*nativeA+(nativeRaw 962).2.2,
  nativeAvg*nativeA+(nativeRaw 963).2.2,
  nativeAvg*nativeA+(nativeRaw 964).2.2,
  nativeAvg*nativeA+(nativeRaw 965).2.2,
  nativeAvg*nativeA+(nativeRaw 966).2.2,
  nativeAvg*nativeA+(nativeRaw 967).2.2,
  nativeAvg*nativeA+(nativeRaw 968).2.2
]

def nativeHistoryStrong0928Start : ℚ × ℚ := ((960865667179053422125864697785571/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(380602506334511234302303271551583711595811232160393674661817459318050862121009716681271080737754453/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0928End : ℚ × ℚ := ((9851689022750082313854784888569/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1189382832295347607194697723598699098736910100501230233318179913048938314671742186382551259356242559/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0928Inputs_length : nativeHistoryStrong0928Inputs.length = 32 := rfl

theorem nativeHistoryStrong0928Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(937+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(937+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0928Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0928Inputs.getD i.val 0)*(nativeHistoryStrong0928Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0928_checked : nativeHistorySteps 9 928 32 nativeHistoryStrong0928Inputs nativeHistoryStrong0928Start = nativeHistoryStrong0928End := by
  decide +kernel

theorem nativeHistoryStrong0928Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0928Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0928Weight : nativeHistoryRatio^928 ≤ nativeHistoryStrong0928Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0928Real_bound : nativeHistoryReal 9 928 nativeHistoryStrong0928Inputs ≤ (nativeHistoryStrong0928End.2 : ℝ)-(nativeHistoryStrong0928Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0928Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0928Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0928Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0928Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0928Inputs.length) := nativeHistoryStrong0928Domains ⟨i,by simpa only [nativeHistoryStrong0928Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0928Inputs.length) := nativeHistoryStrong0928Roots ⟨i,by simpa only [nativeHistoryStrong0928Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0928Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 928 nativeHistoryStrong0928Inputs nativeHistoryStrong0928Start ht hd hr hw
  simpa only [nativeHistoryStrong0928Inputs_length,nativeHistoryStrong0928_checked] using hs

end ASDExplicitGamma.Numerics.Native
