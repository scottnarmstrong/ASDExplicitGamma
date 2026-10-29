module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0672Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 721).2.2,
  nativeAvg*nativeA+(nativeRaw 722).2.2,
  nativeAvg*nativeA+(nativeRaw 723).2.2,
  nativeAvg*nativeA+(nativeRaw 724).2.2,
  nativeAvg*nativeA+(nativeRaw 725).2.2,
  nativeAvg*nativeA+(nativeRaw 726).2.2,
  nativeAvg*nativeA+(nativeRaw 727).2.2,
  nativeAvg*nativeA+(nativeRaw 728).2.2,
  nativeAvg*nativeA+(nativeRaw 729).2.2,
  nativeAvg*nativeA+(nativeRaw 730).2.2,
  nativeAvg*nativeA+(nativeRaw 731).2.2,
  nativeAvg*nativeA+(nativeRaw 732).2.2,
  nativeAvg*nativeA+(nativeRaw 733).2.2,
  nativeAvg*nativeA+(nativeRaw 734).2.2,
  nativeAvg*nativeA+(nativeRaw 735).2.2,
  nativeAvg*nativeA+(nativeRaw 736).2.2,
  nativeAvg*nativeA+(nativeRaw 737).2.2,
  nativeAvg*nativeA+(nativeRaw 738).2.2,
  nativeAvg*nativeA+(nativeRaw 739).2.2,
  nativeAvg*nativeA+(nativeRaw 740).2.2,
  nativeAvg*nativeA+(nativeRaw 741).2.2,
  nativeAvg*nativeA+(nativeRaw 742).2.2,
  nativeAvg*nativeA+(nativeRaw 743).2.2,
  nativeAvg*nativeA+(nativeRaw 744).2.2,
  nativeAvg*nativeA+(nativeRaw 745).2.2,
  nativeAvg*nativeA+(nativeRaw 746).2.2,
  nativeAvg*nativeA+(nativeRaw 747).2.2,
  nativeAvg*nativeA+(nativeRaw 748).2.2,
  nativeAvg*nativeA+(nativeRaw 749).2.2,
  nativeAvg*nativeA+(nativeRaw 750).2.2,
  nativeAvg*nativeA+(nativeRaw 751).2.2,
  nativeAvg*nativeA+(nativeRaw 752).2.2
]

def nativeHistoryBuffer0672Start : ℚ × ℚ := ((8057094976550511245455887406884759508833090707909009/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11713264740679284981361132629107474896907695555145955204407052557965439716437504986349051376374205061/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0672End : ℚ × ℚ := ((20652208952572063530353586293551055026351481363117/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687242269239552398322525322648170796540631416139103201562065296819737/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0672Inputs_length : nativeHistoryBuffer0672Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0672Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(721+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(721+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0672Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0672Inputs.getD i.val 0)*(nativeHistoryBuffer0672Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0672_checked : nativeHistorySteps 49 672 32 nativeHistoryBuffer0672Inputs nativeHistoryBuffer0672Start = nativeHistoryBuffer0672End := by
  decide +kernel

theorem nativeHistoryBuffer0672Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0672Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0672Weight : nativeHistoryRatio^672 ≤ nativeHistoryBuffer0672Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0672Real_bound : nativeHistoryReal 49 672 nativeHistoryBuffer0672Inputs ≤ (nativeHistoryBuffer0672End.2 : ℝ)-(nativeHistoryBuffer0672Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0672Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0672Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0672Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0672Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0672Inputs.length) := nativeHistoryBuffer0672Domains ⟨i,by simpa only [nativeHistoryBuffer0672Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0672Inputs.length) := nativeHistoryBuffer0672Roots ⟨i,by simpa only [nativeHistoryBuffer0672Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0672Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 672 nativeHistoryBuffer0672Inputs nativeHistoryBuffer0672Start ht hd hr hw
  simpa only [nativeHistoryBuffer0672Inputs_length,nativeHistoryBuffer0672_checked] using hs

end ASDExplicitGamma.Numerics.Native
