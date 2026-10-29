module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B59 : ModeBlockData :=
  ⟨⟨59, 60, (5424713026979603089/1000000000000000000000 : ℚ), (1418878384277980947/10000000000000000000000 : ℚ)⟩, [
    (59, modeDataJ3M60)], (54247130269796030889/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b59 : entryChecks 3 bflatBlockJ3B59.entries = true := by
  simp only [entryChecks,bflatBlockJ3B59,List.all_cons,List.all_nil,
    mode_checked_j3_m60,Bool.and_self]
theorem block_mass_checked_j3_b59 : blockMassCheck bflatBlockJ3B59 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
