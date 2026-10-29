module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0768Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 777).2.2,
  nativeAvg*nativeA+(nativeRaw 778).2.2,
  nativeAvg*nativeA+(nativeRaw 779).2.2,
  nativeAvg*nativeA+(nativeRaw 780).2.2,
  nativeAvg*nativeA+(nativeRaw 781).2.2,
  nativeAvg*nativeA+(nativeRaw 782).2.2,
  nativeAvg*nativeA+(nativeRaw 783).2.2,
  nativeAvg*nativeA+(nativeRaw 784).2.2,
  nativeAvg*nativeA+(nativeRaw 785).2.2,
  nativeAvg*nativeA+(nativeRaw 786).2.2,
  nativeAvg*nativeA+(nativeRaw 787).2.2,
  nativeAvg*nativeA+(nativeRaw 788).2.2,
  nativeAvg*nativeA+(nativeRaw 789).2.2,
  nativeAvg*nativeA+(nativeRaw 790).2.2,
  nativeAvg*nativeA+(nativeRaw 791).2.2,
  nativeAvg*nativeA+(nativeRaw 792).2.2,
  nativeAvg*nativeA+(nativeRaw 793).2.2,
  nativeAvg*nativeA+(nativeRaw 794).2.2,
  nativeAvg*nativeA+(nativeRaw 795).2.2,
  nativeAvg*nativeA+(nativeRaw 796).2.2,
  nativeAvg*nativeA+(nativeRaw 797).2.2,
  nativeAvg*nativeA+(nativeRaw 798).2.2,
  nativeAvg*nativeA+(nativeRaw 799).2.2,
  nativeAvg*nativeA+(nativeRaw 800).2.2,
  nativeAvg*nativeA+(nativeRaw 801).2.2,
  nativeAvg*nativeA+(nativeRaw 802).2.2,
  nativeAvg*nativeA+(nativeRaw 803).2.2,
  nativeAvg*nativeA+(nativeRaw 804).2.2,
  nativeAvg*nativeA+(nativeRaw 805).2.2,
  nativeAvg*nativeA+(nativeRaw 806).2.2,
  nativeAvg*nativeA+(nativeRaw 807).2.2,
  nativeAvg*nativeA+(nativeRaw 808).2.2
]

def nativeHistoryStrong0768Start : ℚ × ℚ := ((1085506809381912300733748395090105166085320679/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820201002397227417100121608468092959597929663256766041782217/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0768End : ℚ × ℚ := ((1391203250801999705329508869525379513380709/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280804009840272809242789049253300839235915662872578114489903/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0768Inputs_length : nativeHistoryStrong0768Inputs.length = 32 := rfl

theorem nativeHistoryStrong0768Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(777+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(777+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0768Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0768Inputs.getD i.val 0)*(nativeHistoryStrong0768Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0768_checked : nativeHistorySteps 9 768 32 nativeHistoryStrong0768Inputs nativeHistoryStrong0768Start = nativeHistoryStrong0768End := by
  decide +kernel

theorem nativeHistoryStrong0768Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0768Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0768Weight : nativeHistoryRatio^768 ≤ nativeHistoryStrong0768Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0768Real_bound : nativeHistoryReal 9 768 nativeHistoryStrong0768Inputs ≤ (nativeHistoryStrong0768End.2 : ℝ)-(nativeHistoryStrong0768Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0768Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0768Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0768Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0768Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0768Inputs.length) := nativeHistoryStrong0768Domains ⟨i,by simpa only [nativeHistoryStrong0768Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0768Inputs.length) := nativeHistoryStrong0768Roots ⟨i,by simpa only [nativeHistoryStrong0768Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0768Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 768 nativeHistoryStrong0768Inputs nativeHistoryStrong0768Start ht hd hr hw
  simpa only [nativeHistoryStrong0768Inputs_length,nativeHistoryStrong0768_checked] using hs

end ASDExplicitGamma.Numerics.Native
