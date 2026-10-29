module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B16 : ModeBlockData :=
  ⟨⟨16, 17, (2041321188659749587/1250000000000000000000 : ℚ), (14840557426538563633/10000000000000000000000 : ℚ)⟩, [
    (16, modeDataJ1M17)], (3266113901855599339/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b16 : entryChecks 1 bflatBlockJ1B16.entries = true := by
  simp only [entryChecks,bflatBlockJ1B16,List.all_cons,List.all_nil,
    mode_checked_j1_m17,Bool.and_self]
theorem block_mass_checked_j1_b16 : blockMassCheck bflatBlockJ1B16 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
