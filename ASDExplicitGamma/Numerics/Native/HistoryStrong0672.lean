module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0672Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 681).2.2,
  nativeAvg*nativeA+(nativeRaw 682).2.2,
  nativeAvg*nativeA+(nativeRaw 683).2.2,
  nativeAvg*nativeA+(nativeRaw 684).2.2,
  nativeAvg*nativeA+(nativeRaw 685).2.2,
  nativeAvg*nativeA+(nativeRaw 686).2.2,
  nativeAvg*nativeA+(nativeRaw 687).2.2,
  nativeAvg*nativeA+(nativeRaw 688).2.2,
  nativeAvg*nativeA+(nativeRaw 689).2.2,
  nativeAvg*nativeA+(nativeRaw 690).2.2,
  nativeAvg*nativeA+(nativeRaw 691).2.2,
  nativeAvg*nativeA+(nativeRaw 692).2.2,
  nativeAvg*nativeA+(nativeRaw 693).2.2,
  nativeAvg*nativeA+(nativeRaw 694).2.2,
  nativeAvg*nativeA+(nativeRaw 695).2.2,
  nativeAvg*nativeA+(nativeRaw 696).2.2,
  nativeAvg*nativeA+(nativeRaw 697).2.2,
  nativeAvg*nativeA+(nativeRaw 698).2.2,
  nativeAvg*nativeA+(nativeRaw 699).2.2,
  nativeAvg*nativeA+(nativeRaw 700).2.2,
  nativeAvg*nativeA+(nativeRaw 701).2.2,
  nativeAvg*nativeA+(nativeRaw 702).2.2,
  nativeAvg*nativeA+(nativeRaw 703).2.2,
  nativeAvg*nativeA+(nativeRaw 704).2.2,
  nativeAvg*nativeA+(nativeRaw 705).2.2,
  nativeAvg*nativeA+(nativeRaw 706).2.2,
  nativeAvg*nativeA+(nativeRaw 707).2.2,
  nativeAvg*nativeA+(nativeRaw 708).2.2,
  nativeAvg*nativeA+(nativeRaw 709).2.2,
  nativeAvg*nativeA+(nativeRaw 710).2.2,
  nativeAvg*nativeA+(nativeRaw 711).2.2,
  nativeAvg*nativeA+(nativeRaw 712).2.2
]

def nativeHistoryStrong0672Start : ℚ × ℚ := ((8057094976550511245455887406884759508833090707909009/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895279739454572010655506146326876721211970731069283925113367447/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0672End : ℚ × ℚ := ((20652208952572063530353586293551055026351481363117/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820199366343960684409651362754656173187627467373373294180133/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0672Inputs_length : nativeHistoryStrong0672Inputs.length = 32 := rfl

theorem nativeHistoryStrong0672Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(681+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(681+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0672Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0672Inputs.getD i.val 0)*(nativeHistoryStrong0672Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0672_checked : nativeHistorySteps 9 672 32 nativeHistoryStrong0672Inputs nativeHistoryStrong0672Start = nativeHistoryStrong0672End := by
  decide +kernel

theorem nativeHistoryStrong0672Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0672Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0672Weight : nativeHistoryRatio^672 ≤ nativeHistoryStrong0672Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0672Real_bound : nativeHistoryReal 9 672 nativeHistoryStrong0672Inputs ≤ (nativeHistoryStrong0672End.2 : ℝ)-(nativeHistoryStrong0672Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0672Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0672Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0672Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0672Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0672Inputs.length) := nativeHistoryStrong0672Domains ⟨i,by simpa only [nativeHistoryStrong0672Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0672Inputs.length) := nativeHistoryStrong0672Roots ⟨i,by simpa only [nativeHistoryStrong0672Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0672Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 672 nativeHistoryStrong0672Inputs nativeHistoryStrong0672Start ht hd hr hw
  simpa only [nativeHistoryStrong0672Inputs_length,nativeHistoryStrong0672_checked] using hs

end ASDExplicitGamma.Numerics.Native
