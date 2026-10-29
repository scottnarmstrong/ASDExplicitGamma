module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B22 : ModeBlockData :=
  ⟨⟨22, 23, (8174424863729924961/10000000000000000000000 : ℚ), (1971344024002164959/2500000000000000000000 : ℚ)⟩, [
    (22, modeDataJ1M23)], (51090155398312031/62500000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b22 : entryChecks 1 bflatBlockJ1B22.entries = true := by
  simp only [entryChecks,bflatBlockJ1B22,List.all_cons,List.all_nil,
    mode_checked_j1_m23,Bool.and_self]
theorem block_mass_checked_j1_b22 : blockMassCheck bflatBlockJ1B22 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
