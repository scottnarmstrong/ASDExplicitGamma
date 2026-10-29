module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B51 : ModeBlockData :=
  ⟨⟨51, 52, (78909164588277261489/10000000000000000000000 : ℚ), (1719281112425827927/10000000000000000000000 : ℚ)⟩, [
    (51, modeDataJ3M52)], (4931822786767328843/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b51 : entryChecks 3 bflatBlockJ3B51.entries = true := by
  simp only [entryChecks,bflatBlockJ3B51,List.all_cons,List.all_nil,
    mode_checked_j3_m52,Bool.and_self]
theorem block_mass_checked_j3_b51 : blockMassCheck bflatBlockJ3B51 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
