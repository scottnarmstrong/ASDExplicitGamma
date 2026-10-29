module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0704Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 713).2.2,
  nativeAvg*nativeA+(nativeRaw 714).2.2,
  nativeAvg*nativeA+(nativeRaw 715).2.2,
  nativeAvg*nativeA+(nativeRaw 716).2.2,
  nativeAvg*nativeA+(nativeRaw 717).2.2,
  nativeAvg*nativeA+(nativeRaw 718).2.2,
  nativeAvg*nativeA+(nativeRaw 719).2.2,
  nativeAvg*nativeA+(nativeRaw 720).2.2,
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
  nativeAvg*nativeA+(nativeRaw 744).2.2
]

def nativeHistoryStrong0704Start : ℚ × ℚ := ((20652208952572063530353586293551055026351481363117/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(2378765664590695214389395447197398197473820199366343960684409651362754656173187627467373373294180133/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0704End : ℚ × ℚ := ((211745665583950339626510461958685185293939777539/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9515062658362780857557581788789592789895280803969319527643060308498324408557495750417431634006823457/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0704Inputs_length : nativeHistoryStrong0704Inputs.length = 32 := rfl

theorem nativeHistoryStrong0704Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(713+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(713+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0704Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0704Inputs.getD i.val 0)*(nativeHistoryStrong0704Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0704_checked : nativeHistorySteps 9 704 32 nativeHistoryStrong0704Inputs nativeHistoryStrong0704Start = nativeHistoryStrong0704End := by
  decide +kernel

theorem nativeHistoryStrong0704Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0704Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0704Weight : nativeHistoryRatio^704 ≤ nativeHistoryStrong0704Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0704Real_bound : nativeHistoryReal 9 704 nativeHistoryStrong0704Inputs ≤ (nativeHistoryStrong0704End.2 : ℝ)-(nativeHistoryStrong0704Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0704Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0704Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0704Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0704Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0704Inputs.length) := nativeHistoryStrong0704Domains ⟨i,by simpa only [nativeHistoryStrong0704Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0704Inputs.length) := nativeHistoryStrong0704Roots ⟨i,by simpa only [nativeHistoryStrong0704Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0704Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 704 nativeHistoryStrong0704Inputs nativeHistoryStrong0704Start ht hd hr hw
  simpa only [nativeHistoryStrong0704Inputs_length,nativeHistoryStrong0704_checked] using hs

end ASDExplicitGamma.Numerics.Native
