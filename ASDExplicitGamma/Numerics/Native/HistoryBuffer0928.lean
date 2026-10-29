module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0928Inputs : List ℚ := [
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
  nativeAvg*nativeA+(nativeRaw 1000).2.2,
  nativeAvg*nativeA+(nativeRaw 1001).2.2,
  nativeAvg*nativeA+(nativeRaw 1002).2.2,
  nativeAvg*nativeA+(nativeRaw 1003).2.2,
  nativeAvg*nativeA+(nativeRaw 1004).2.2,
  nativeAvg*nativeA+(nativeRaw 1005).2.2,
  nativeAvg*nativeA+(nativeRaw 1006).2.2,
  nativeAvg*nativeA+(nativeRaw 1007).2.2,
  nativeAvg*nativeA+(nativeRaw 1008).2.2
]

def nativeHistoryBuffer0928Start : ℚ × ℚ := ((960865667179053422125864697785571/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093455721366930962635351665766188035353279138515323429/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0928End : ℚ × ℚ := ((9851689022750082313854784888569/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(14641580925849106226701415786384343621134619778273363930341733743253465594759782962129389045612338077/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0928Inputs_length : nativeHistoryBuffer0928Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0928Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(977+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(977+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0928Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0928Inputs.getD i.val 0)*(nativeHistoryBuffer0928Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0928_checked : nativeHistorySteps 49 928 32 nativeHistoryBuffer0928Inputs nativeHistoryBuffer0928Start = nativeHistoryBuffer0928End := by
  decide +kernel

theorem nativeHistoryBuffer0928Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0928Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0928Weight : nativeHistoryRatio^928 ≤ nativeHistoryBuffer0928Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0928Real_bound : nativeHistoryReal 49 928 nativeHistoryBuffer0928Inputs ≤ (nativeHistoryBuffer0928End.2 : ℝ)-(nativeHistoryBuffer0928Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0928Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0928Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0928Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0928Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0928Inputs.length) := nativeHistoryBuffer0928Domains ⟨i,by simpa only [nativeHistoryBuffer0928Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0928Inputs.length) := nativeHistoryBuffer0928Roots ⟨i,by simpa only [nativeHistoryBuffer0928Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0928Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 928 nativeHistoryBuffer0928Inputs nativeHistoryBuffer0928Start ht hd hr hw
  simpa only [nativeHistoryBuffer0928Inputs_length,nativeHistoryBuffer0928_checked] using hs

end ASDExplicitGamma.Numerics.Native
