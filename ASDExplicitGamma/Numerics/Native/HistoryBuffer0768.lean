module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0768Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 817).2.2,
  nativeAvg*nativeA+(nativeRaw 818).2.2,
  nativeAvg*nativeA+(nativeRaw 819).2.2,
  nativeAvg*nativeA+(nativeRaw 820).2.2,
  nativeAvg*nativeA+(nativeRaw 821).2.2,
  nativeAvg*nativeA+(nativeRaw 822).2.2,
  nativeAvg*nativeA+(nativeRaw 823).2.2,
  nativeAvg*nativeA+(nativeRaw 824).2.2,
  nativeAvg*nativeA+(nativeRaw 825).2.2,
  nativeAvg*nativeA+(nativeRaw 826).2.2,
  nativeAvg*nativeA+(nativeRaw 827).2.2,
  nativeAvg*nativeA+(nativeRaw 828).2.2,
  nativeAvg*nativeA+(nativeRaw 829).2.2,
  nativeAvg*nativeA+(nativeRaw 830).2.2,
  nativeAvg*nativeA+(nativeRaw 831).2.2,
  nativeAvg*nativeA+(nativeRaw 832).2.2,
  nativeAvg*nativeA+(nativeRaw 833).2.2,
  nativeAvg*nativeA+(nativeRaw 834).2.2,
  nativeAvg*nativeA+(nativeRaw 835).2.2,
  nativeAvg*nativeA+(nativeRaw 836).2.2,
  nativeAvg*nativeA+(nativeRaw 837).2.2,
  nativeAvg*nativeA+(nativeRaw 838).2.2,
  nativeAvg*nativeA+(nativeRaw 839).2.2,
  nativeAvg*nativeA+(nativeRaw 840).2.2,
  nativeAvg*nativeA+(nativeRaw 841).2.2,
  nativeAvg*nativeA+(nativeRaw 842).2.2,
  nativeAvg*nativeA+(nativeRaw 843).2.2,
  nativeAvg*nativeA+(nativeRaw 844).2.2,
  nativeAvg*nativeA+(nativeRaw 845).2.2,
  nativeAvg*nativeA+(nativeRaw 846).2.2,
  nativeAvg*nativeA+(nativeRaw 847).2.2,
  nativeAvg*nativeA+(nativeRaw 848).2.2
]

def nativeHistoryBuffer0768Start : ℚ × ℚ := ((1085506809381912300733748395090105166085320679/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093127868371996448608955037226353599191282581351810919/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0768End : ℚ × ℚ := ((1391203250801999705329508869525379513380709/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(58566323703396424906805663145537374484538479113093453627784085286157945817600804624780467881841751029/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0768Inputs_length : nativeHistoryBuffer0768Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0768Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(817+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(817+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0768Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0768Inputs.getD i.val 0)*(nativeHistoryBuffer0768Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0768_checked : nativeHistorySteps 49 768 32 nativeHistoryBuffer0768Inputs nativeHistoryBuffer0768Start = nativeHistoryBuffer0768End := by
  decide +kernel

theorem nativeHistoryBuffer0768Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0768Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0768Weight : nativeHistoryRatio^768 ≤ nativeHistoryBuffer0768Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0768Real_bound : nativeHistoryReal 49 768 nativeHistoryBuffer0768Inputs ≤ (nativeHistoryBuffer0768End.2 : ℝ)-(nativeHistoryBuffer0768Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0768Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0768Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0768Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0768Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0768Inputs.length) := nativeHistoryBuffer0768Domains ⟨i,by simpa only [nativeHistoryBuffer0768Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0768Inputs.length) := nativeHistoryBuffer0768Roots ⟨i,by simpa only [nativeHistoryBuffer0768Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0768Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 768 nativeHistoryBuffer0768Inputs nativeHistoryBuffer0768Start ht hd hr hw
  simpa only [nativeHistoryBuffer0768Inputs_length,nativeHistoryBuffer0768_checked] using hs

end ASDExplicitGamma.Numerics.Native
