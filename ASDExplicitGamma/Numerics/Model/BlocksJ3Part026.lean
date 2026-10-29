module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B26 : ModeBlockData :=
  ⟨⟨26, 27, (172411449544383090899/10000000000000000000000 : ℚ), (2693184568610149051/10000000000000000000000 : ℚ)⟩, [
    (26, modeDataJ3M27)], (86205724772191545449/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b26 : entryChecks 3 bflatBlockJ3B26.entries = true := by
  simp only [entryChecks,bflatBlockJ3B26,List.all_cons,List.all_nil,
    mode_checked_j3_m27,Bool.and_self]
theorem block_mass_checked_j3_b26 : blockMassCheck bflatBlockJ3B26 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
