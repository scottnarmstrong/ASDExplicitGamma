module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
public import ASDExplicitGamma.Numerics.Native.Heat073Passes
public import ASDExplicitGamma.Numerics.Native.Heat074Passes
public import ASDExplicitGamma.Numerics.Native.Heat075Passes
public import ASDExplicitGamma.Numerics.Native.Heat076Passes
public import ASDExplicitGamma.Numerics.Native.Heat077Passes
public import ASDExplicitGamma.Numerics.Native.Heat078Passes
public import ASDExplicitGamma.Numerics.Native.Heat079Passes
public import ASDExplicitGamma.Numerics.Native.Heat080Passes
public import ASDExplicitGamma.Numerics.Native.Heat081Passes
public import ASDExplicitGamma.Numerics.Native.Heat082Passes
public import ASDExplicitGamma.Numerics.Native.Heat083Passes
public import ASDExplicitGamma.Numerics.Native.Heat084Passes
public import ASDExplicitGamma.Numerics.Native.Heat085Passes
public import ASDExplicitGamma.Numerics.Native.Heat086Passes
public import ASDExplicitGamma.Numerics.Native.Heat087Passes
public import ASDExplicitGamma.Numerics.Native.Heat088Passes
public import ASDExplicitGamma.Numerics.Native.Heat089Passes
public import ASDExplicitGamma.Numerics.Native.Heat090Passes
public import ASDExplicitGamma.Numerics.Native.Heat091Passes
public import ASDExplicitGamma.Numerics.Native.Heat092Passes
public import ASDExplicitGamma.Numerics.Native.Heat093Passes
public import ASDExplicitGamma.Numerics.Native.Heat094Passes
public import ASDExplicitGamma.Numerics.Native.Heat095Passes
public import ASDExplicitGamma.Numerics.Native.Heat096Passes
public import ASDExplicitGamma.Numerics.Native.Heat097Passes
public import ASDExplicitGamma.Numerics.Native.Heat098Passes
public import ASDExplicitGamma.Numerics.Native.Heat099Passes
public import ASDExplicitGamma.Numerics.Native.Heat100Passes
public import ASDExplicitGamma.Numerics.Native.Heat101Passes
public import ASDExplicitGamma.Numerics.Native.Heat102Passes
public import ASDExplicitGamma.Numerics.Native.Heat103Passes
public import ASDExplicitGamma.Numerics.Native.Heat104Passes
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryStrong0064Inputs : List ℚ := [
  nativeHeat073Result.1,
  nativeHeat074Result.1,
  nativeHeat075Result.1,
  nativeHeat076Result.1,
  nativeHeat077Result.1,
  nativeHeat078Result.1,
  nativeHeat079Result.1,
  nativeHeat080Result.1,
  nativeHeat081Result.1,
  nativeHeat082Result.1,
  nativeHeat083Result.1,
  nativeHeat084Result.1,
  nativeHeat085Result.1,
  nativeHeat086Result.1,
  nativeHeat087Result.1,
  nativeHeat088Result.1,
  nativeHeat089Result.1,
  nativeHeat090Result.1,
  nativeHeat091Result.1,
  nativeHeat092Result.1,
  nativeHeat093Result.1,
  nativeHeat094Result.1,
  nativeHeat095Result.1,
  nativeHeat096Result.1,
  nativeHeat097Result.1,
  nativeHeat098Result.1,
  nativeHeat099Result.1,
  nativeHeat100Result.1,
  nativeHeat101Result.1,
  nativeHeat102Result.1,
  nativeHeat103Result.1,
  nativeHeat104Result.1
]

def nativeHistoryStrong0064Start : ℚ × ℚ := ((131403232927139413270943018109166438266671843519464140309185193811127222747299756757232797091897/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(9512667185420404753235360374110163013897140776143070431121952336756679728155604459019362127403067737/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryStrong0064End : ℚ × ℚ := ((53890729228893908948650697579230642336746572461746780685585969132785895404612208062887595381/400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(4757521258969907276295890060294315921035934065314709990287111262669674550484330835229185817148366651/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryStrong0064Inputs_length : nativeHistoryStrong0064Inputs.length = 32 := rfl

theorem nativeHistoryStrong0064Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(73+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(73+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryStrong0064Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryStrong0064Inputs.getD i.val 0)*(nativeHistoryStrong0064Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryStrong0064_checked : nativeHistorySteps 9 64 32 nativeHistoryStrong0064Inputs nativeHistoryStrong0064Start = nativeHistoryStrong0064End := by
  decide +kernel

theorem nativeHistoryStrong0064Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryStrong0064Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryStrong0064Weight : nativeHistoryRatio^64 ≤ nativeHistoryStrong0064Start.1 := by
  decide +kernel

theorem nativeHistoryStrong0064Real_bound : nativeHistoryReal 9 64 nativeHistoryStrong0064Inputs ≤ (nativeHistoryStrong0064End.2 : ℝ)-(nativeHistoryStrong0064Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryStrong0064Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryStrong0064Inputs_nonneg ⟨i,by simpa only [nativeHistoryStrong0064Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryStrong0064Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryStrong0064Inputs.length) := nativeHistoryStrong0064Domains ⟨i,by simpa only [nativeHistoryStrong0064Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryStrong0064Inputs.length) := nativeHistoryStrong0064Roots ⟨i,by simpa only [nativeHistoryStrong0064Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryStrong0064Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 9 64 nativeHistoryStrong0064Inputs nativeHistoryStrong0064Start ht hd hr hw
  simpa only [nativeHistoryStrong0064Inputs_length,nativeHistoryStrong0064_checked] using hs

end ASDExplicitGamma.Numerics.Native
