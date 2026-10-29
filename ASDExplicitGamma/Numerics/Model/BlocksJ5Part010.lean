module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B10 : ModeBlockData :=
  ⟨⟨10, 11, (25206307795683837853/10000000000000000000000 : ℚ), (7900220942990007/2000000000000000000000 : ℚ)⟩, [
    (10, modeDataJ5M11)], (6301576948920959463/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b10 : entryChecks 5 bflatBlockJ5B10.entries = true := by
  simp only [entryChecks,bflatBlockJ5B10,List.all_cons,List.all_nil,
    mode_checked_j5_m11,Bool.and_self]
theorem block_mass_checked_j5_b10 : blockMassCheck bflatBlockJ5B10 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
