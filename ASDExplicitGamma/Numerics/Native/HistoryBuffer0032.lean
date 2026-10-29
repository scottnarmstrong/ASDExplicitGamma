module
public import ASDExplicitGamma.Numerics.Native.HistorySoundness
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
public import ASDExplicitGamma.Numerics.Native.Heat105Passes
public import ASDExplicitGamma.Numerics.Native.Heat106Passes
public import ASDExplicitGamma.Numerics.Native.Heat107Passes
public import ASDExplicitGamma.Numerics.Native.Heat108Passes
public import ASDExplicitGamma.Numerics.Native.Heat109Passes
public import ASDExplicitGamma.Numerics.Native.Heat110Passes
public import ASDExplicitGamma.Numerics.Native.Heat111Passes
public import ASDExplicitGamma.Numerics.Native.Heat112Passes
/-! Consecutive complete native history terms, including the raw branch after depth 160. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeHistoryBuffer0032Inputs : List ℚ := [
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
  nativeHeat104Result.1,
  nativeHeat105Result.1,
  nativeHeat106Result.1,
  nativeHeat107Result.1,
  nativeHeat108Result.1,
  nativeHeat109Result.1,
  nativeHeat110Result.1,
  nativeHeat111Result.1,
  nativeHeat112Result.1
]

def nativeHistoryBuffer0032Start : ℚ × ℚ := ((51264653110528196233010474094698914761560440183286109130721933663896264646506431396097970427500063/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(11607972432150672026522436717775641623668026233449521444730673195884526282693605836931284699422517573/2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))
def nativeHistoryBuffer0032End : ℚ × ℚ := ((131403232927139413270943018109166438266671843519464140309185193811127222747299756757232797091897/5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ),(7320158266941163935353072257755758136301983275035737054823946522768778197067237372531847155465579199/1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ))

theorem nativeHistoryBuffer0032Inputs_length : nativeHistoryBuffer0032Inputs.length = 32 := rfl

theorem nativeHistoryBuffer0032Domains : ∀ i : Fin 32, 0 ≤ (11/10)*(2*nativeGamma*(81+i.val : ℕ)) ∧ (11/10)*(2*nativeGamma*(81+i.val : ℕ)) < 1 := by
  decide +kernel

theorem nativeHistoryBuffer0032Roots : ∀ i : Fin 32, nativeRootValid ((nativeHistoryBuffer0032Inputs.getD i.val 0)*(nativeHistoryBuffer0032Inputs.getD i.val 0+8)) 2 = true := by
  decide +kernel

theorem nativeHistoryBuffer0032_checked : nativeHistorySteps 49 32 32 nativeHistoryBuffer0032Inputs nativeHistoryBuffer0032Start = nativeHistoryBuffer0032End := by
  decide +kernel

theorem nativeHistoryBuffer0032Inputs_nonneg : ∀ i : Fin 32, 0 ≤ nativeHistoryBuffer0032Inputs.getD i.val 0 := by
  decide +kernel

theorem nativeHistoryBuffer0032Weight : nativeHistoryRatio^32 ≤ nativeHistoryBuffer0032Start.1 := by
  decide +kernel

theorem nativeHistoryBuffer0032Real_bound : nativeHistoryReal 49 32 nativeHistoryBuffer0032Inputs ≤ (nativeHistoryBuffer0032End.2 : ℝ)-(nativeHistoryBuffer0032Start.2 : ℝ) := by
  have ht (t : ℚ) (ht : t ∈ nativeHistoryBuffer0032Inputs) : 0 ≤ t := by
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem ht
    have h := nativeHistoryBuffer0032Inputs_nonneg ⟨i,by simpa only [nativeHistoryBuffer0032Inputs_length] using hi⟩
    simpa only [List.getD_eq_getElem nativeHistoryBuffer0032Inputs 0 hi,hix] using h
  have hd (i : ℕ) (hi : i < nativeHistoryBuffer0032Inputs.length) := nativeHistoryBuffer0032Domains ⟨i,by simpa only [nativeHistoryBuffer0032Inputs_length] using hi⟩
  have hr (i : ℕ) (hi : i < nativeHistoryBuffer0032Inputs.length) := nativeHistoryBuffer0032Roots ⟨i,by simpa only [nativeHistoryBuffer0032Inputs_length] using hi⟩
  have hw := (Rat.cast_le (K := ℝ)).2 nativeHistoryBuffer0032Weight
  simp only [Rat.cast_pow] at hw
  have hs := nativeHistorySteps_sound 49 32 nativeHistoryBuffer0032Inputs nativeHistoryBuffer0032Start ht hd hr hw
  simpa only [nativeHistoryBuffer0032Inputs_length,nativeHistoryBuffer0032_checked] using hs

end ASDExplicitGamma.Numerics.Native
