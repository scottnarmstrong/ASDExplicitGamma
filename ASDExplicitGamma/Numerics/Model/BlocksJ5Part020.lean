module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B20 : ModeBlockData :=
  ⟨⟨20, 21, (3146114887236000221/1250000000000000000000 : ℚ), (39463841516714521/10000000000000000000000 : ℚ)⟩, [
    (20, modeDataJ5M21)], (25168919097888001767/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b20 : entryChecks 5 bflatBlockJ5B20.entries = true := by
  simp only [entryChecks,bflatBlockJ5B20,List.all_cons,List.all_nil,
    mode_checked_j5_m21,Bool.and_self]
theorem block_mass_checked_j5_b20 : blockMassCheck bflatBlockJ5B20 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
