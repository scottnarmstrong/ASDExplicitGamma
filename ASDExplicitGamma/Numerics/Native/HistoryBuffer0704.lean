module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0704Inputs : List ℚ := [
  nativeAvg*nativeA+(nativeRaw 753).2.2,
  nativeAvg*nativeA+(nativeRaw 754).2.2,
  nativeAvg*nativeA+(nativeRaw 755).2.2,
  nativeAvg*nativeA+(nativeRaw 756).2.2,
  nativeAvg*nativeA+(nativeRaw 757).2.2,
  nativeAvg*nativeA+(nativeRaw 758).2.2,
  nativeAvg*nativeA+(nativeRaw 759).2.2,
  nativeAvg*nativeA+(nativeRaw 760).2.2,
  nativeAvg*nativeA+(nativeRaw 761).2.2,
  nativeAvg*nativeA+(nativeRaw 762).2.2,
  nativeAvg*nativeA+(nativeRaw 763).2.2,
  nativeAvg*nativeA+(nativeRaw 764).2.2,
  nativeAvg*nativeA+(nativeRaw 765).2.2,
  nativeAvg*nativeA+(nativeRaw 766).2.2,
  nativeAvg*nativeA+(nativeRaw 767).2.2,
  nativeAvg*nativeA+(nativeRaw 768).2.2,
  nativeAvg*nativeA+(nativeRaw 769).2.2,
  nativeAvg*nativeA+(nativeRaw 770).2.2,
  nativeAvg*nativeA+(nativeRaw 771).2.2,
  nativeAvg*nativeA+(nativeRaw 772).2.2,
  nativeAvg*nativeA+(nativeRaw 773).2.2,
  nativeAvg*nativeA+(nativeRaw 774).2.2,
  nativeAvg*nativeA+(nativeRaw 775).2.2,
  nativeAvg*nativeA+(nativeRaw 776).2.2,
  nativeAvg*nativeA+(nativeRaw 777).2.2,
  nativeAvg*nativeA+(nativeRaw 778).2.2,
  nativeAvg*nativeA+(nativeRaw 779).2.2,
  nativeAvg*nativeA+(nativeRaw 780).2.2,
  nativeAvg*nativeA+(nativeRaw 781).2.2,
  nativeAvg*nativeA+(nativeRaw 782).2.2,
  nativeAvg*nativeA+(nativeRaw 783).2.2,
  nativeAvg*nativeA+(nativeRaw 784).2.2
]

def nativeHistoryBuffer0704Start : ℚ × ℚ := ((20652208952572063530353586293551055026351481363117/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(29283161851698212453402831572768687242269239552398322525322648170796540631416139103201562065296819737/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0704End : ℚ × ℚ := ((211745665583950339626510461958685185293939777539/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(3660395231462276556675353946596085905283654944565096846700278298249706629093080266976344285204409811/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0704Inputs_length : nativeHistoryBuffer0704Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0704Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(753+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(753+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0704Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0704Inputs.getD i.val 0)*(nativeHistoryBuffer0704Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0704_checked : nativeHistorySteps 49 704 32 nativeHistoryBuffer0704Inputs nativeHistoryBuffer0704Start = nativeHistoryBuffer0704End := by
  decide +kernel

theorem nativeHistoryBuffer0704Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0704Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0704Weight : nativeHistoryRatio^704 ≤ nativeHistoryBuffer0704Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0704Real_bound : nativeHistoryReal 49 704 nativeHistoryBuffer0704Inputs ≤ (nativeHistoryBuffer0704End.2 : ℝ)-(nativeHistoryBuffer0704Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0704Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0704Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0704Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0704Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0704Inputs.length) := nativeHistoryBuffer0704Domains ⟨i,by simpa only [nativeHistoryBuffer0704Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0704Inputs.length) := nativeHistoryBuffer0704Roots ⟨i,by simpa only [nativeHistoryBuffer0704Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0704Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 704 nativeHistoryBuffer0704Inputs nativeHistoryBuffer0704Start ht hd hr hw
  simpa only [nativeHistoryBuffer0704Inputs_length,nativeHistoryBuffer0704_checked] using hs

end ASDExplicitGamma.Numerics.Native
