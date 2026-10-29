module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0960Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 969).2.2,
  nativeAvg*nativeA+(nativeRaw 970).2.2,
  nativeAvg*nativeA+(nativeRaw 971).2.2,
  nativeAvg*nativeA+(nativeRaw 972).2.2,
  nativeAvg*nativeA+(nativeRaw 973).2.2,
  nativeAvg*nativeA+(nativeRaw 974).2.2,
  nativeAvg*nativeA+(nativeRaw 975).2.2,
  nativeAvg*nativeA+(nativeRaw 976).2.2,
  nativeAvg*nativeA+(nativeRaw 977).2.2,
  nativeAvg*nativeA+(nativeRaw 978).2.2,
  nativeAvg*nativeA+(nativeRaw 979).2.2,
  nativeAvg*nativeA+(nativeRaw 980).2.2,
  nativeAvg*nativeA+(nativeRaw 981).2.2,
  nativeAvg*nativeA+(nativeRaw 982).2.2,
  nativeAvg*nativeA+(nativeRaw 983).2.2,
  nativeAvg*nativeA+(nativeRaw 984).2.2,
  nativeAvg*nativeA+(nativeRaw 985).2.2,
  nativeAvg*nativeA+(nativeRaw 986).2.2,
  nativeAvg*nativeA+(nativeRaw 987).2.2,
  nativeAvg*nativeA+(nativeRaw 988).2.2,
  nativeAvg*nativeA+(nativeRaw 989).2.2,
  nativeAvg*nativeA+(nativeRaw 990).2.2,
  nativeAvg*nativeA+(nativeRaw 991).2.2,
  nativeAvg*nativeA+(nativeRaw 992).2.2,
  nativeAvg*nativeA+(nativeRaw 993).2.2,
  nativeAvg*nativeA+(nativeRaw 994).2.2,
  nativeAvg*nativeA+(nativeRaw 995).2.2,
  nativeAvg*nativeA+(nativeRaw 996).2.2,
  nativeAvg*nativeA+(nativeRaw 997).2.2,
  nativeAvg*nativeA+(nativeRaw 998).2.2,
  nativeAvg*nativeA+(nativeRaw 999).2.2,
  nativeAvg*nativeA+(nativeRaw 1000).2.2
]

def nativeHistoryStrong0960Start : ℚ × ℚ := ((9851689022750082313854784888569/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(1189382832295347607194697723598699098736910100501230233318179913048938314671742186382551259356242559/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0960End : ℚ × ℚ := ((101008684060816298614863785309/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866545439323501807132359915884908865523897972091/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0960Inputs_length : nativeHistoryStrong0960Inputs.length = 32 := rfl

theorem nativeHistoryStrong0960Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(969+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(969+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0960Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0960Inputs.getD i.val 0)*(nativeHistoryStrong0960Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0960_checked : nativeHistorySteps 9 960 32 nativeHistoryStrong0960Inputs nativeHistoryStrong0960Start = nativeHistoryStrong0960End := by
  decide +kernel

theorem nativeHistoryStrong0960Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0960Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0960Weight : nativeHistoryRatio^960 ≤ nativeHistoryStrong0960Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0960Real_bound : nativeHistoryReal 9 960 nativeHistoryStrong0960Inputs ≤ (nativeHistoryStrong0960End.2 : ℝ)-(nativeHistoryStrong0960Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0960Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0960Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0960Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0960Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0960Inputs.length) := nativeHistoryStrong0960Domains ⟨i,by simpa only [nativeHistoryStrong0960Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0960Inputs.length) := nativeHistoryStrong0960Roots ⟨i,by simpa only [nativeHistoryStrong0960Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0960Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 960 nativeHistoryStrong0960Inputs nativeHistoryStrong0960Start ht hd hr hw
  simpa only [nativeHistoryStrong0960Inputs_length,nativeHistoryStrong0960_checked] using hs

end ASDExplicitGamma.Numerics.Native
