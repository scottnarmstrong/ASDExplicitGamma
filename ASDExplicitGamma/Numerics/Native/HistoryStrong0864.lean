module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0864Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 873).2.2,
  nativeAvg*nativeA+(nativeRaw 874).2.2,
  nativeAvg*nativeA+(nativeRaw 875).2.2,
  nativeAvg*nativeA+(nativeRaw 876).2.2,
  nativeAvg*nativeA+(nativeRaw 877).2.2,
  nativeAvg*nativeA+(nativeRaw 878).2.2,
  nativeAvg*nativeA+(nativeRaw 879).2.2,
  nativeAvg*nativeA+(nativeRaw 880).2.2,
  nativeAvg*nativeA+(nativeRaw 881).2.2,
  nativeAvg*nativeA+(nativeRaw 882).2.2,
  nativeAvg*nativeA+(nativeRaw 883).2.2,
  nativeAvg*nativeA+(nativeRaw 884).2.2,
  nativeAvg*nativeA+(nativeRaw 885).2.2,
  nativeAvg*nativeA+(nativeRaw 886).2.2,
  nativeAvg*nativeA+(nativeRaw 887).2.2,
  nativeAvg*nativeA+(nativeRaw 888).2.2,
  nativeAvg*nativeA+(nativeRaw 889).2.2,
  nativeAvg*nativeA+(nativeRaw 890).2.2,
  nativeAvg*nativeA+(nativeRaw 891).2.2,
  nativeAvg*nativeA+(nativeRaw 892).2.2,
  nativeAvg*nativeA+(nativeRaw 893).2.2,
  nativeAvg*nativeA+(nativeRaw 894).2.2,
  nativeAvg*nativeA+(nativeRaw 895).2.2,
  nativeAvg*nativeA+(nativeRaw 896).2.2,
  nativeAvg*nativeA+(nativeRaw 897).2.2,
  nativeAvg*nativeA+(nativeRaw 898).2.2,
  nativeAvg*nativeA+(nativeRaw 899).2.2,
  nativeAvg*nativeA+(nativeRaw 900).2.2,
  nativeAvg*nativeA+(nativeRaw 901).2.2,
  nativeAvg*nativeA+(nativeRaw 902).2.2,
  nativeAvg*nativeA+(nativeRaw 903).2.2,
  nativeAvg*nativeA+(nativeRaw 904).2.2
]

def nativeHistoryStrong0864Start : ℚ × ℚ := ((146246883851302975226031747223401938681/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009841866480033755472053348855453256548533180060055691/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0864End : ℚ × ℚ := ((749729576913275489961321993062186813/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820201002460466636252950846870595039842423586421851562558891/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0864Inputs_length : nativeHistoryStrong0864Inputs.length = 32 := rfl

theorem nativeHistoryStrong0864Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(873+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(873+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0864Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0864Inputs.getD i.val 0)*(nativeHistoryStrong0864Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0864_checked : nativeHistorySteps 9 864 32 nativeHistoryStrong0864Inputs nativeHistoryStrong0864Start = nativeHistoryStrong0864End := by
  decide +kernel

theorem nativeHistoryStrong0864Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0864Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0864Weight : nativeHistoryRatio^864 ≤ nativeHistoryStrong0864Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0864Real_bound : nativeHistoryReal 9 864 nativeHistoryStrong0864Inputs ≤ (nativeHistoryStrong0864End.2 : ℝ)-(nativeHistoryStrong0864Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0864Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0864Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0864Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0864Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0864Inputs.length) := nativeHistoryStrong0864Domains ⟨i,by simpa only [nativeHistoryStrong0864Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0864Inputs.length) := nativeHistoryStrong0864Roots ⟨i,by simpa only [nativeHistoryStrong0864Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0864Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 864 nativeHistoryStrong0864Inputs nativeHistoryStrong0864Start ht hd hr hw
  simpa only [nativeHistoryStrong0864Inputs_length,nativeHistoryStrong0864_checked] using hs

end ASDExplicitGamma.Numerics.Native
