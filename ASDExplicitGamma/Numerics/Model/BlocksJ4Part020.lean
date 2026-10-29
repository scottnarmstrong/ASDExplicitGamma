module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B20 : ModeBlockData :=
  ⟨⟨20, 21, (74282857097751544413/10000000000000000000000 : ℚ), (70299998060875689/2000000000000000000000 : ℚ)⟩, [
    (20, modeDataJ4M21)], (18570714274437886103/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b20 : entryChecks 4 bflatBlockJ4B20.entries = true := by
  simp only [entryChecks,bflatBlockJ4B20,List.all_cons,List.all_nil,
    mode_checked_j4_m21,Bool.and_self]
theorem block_mass_checked_j4_b20 : blockMassCheck bflatBlockJ4B20 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
