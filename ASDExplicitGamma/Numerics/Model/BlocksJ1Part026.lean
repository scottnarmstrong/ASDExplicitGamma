module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B26 : ModeBlockData :=
  ⟨⟨26, 27, (580048035001719471/1000000000000000000000 : ℚ), (5674461177539673681/10000000000000000000000 : ℚ)⟩, [
    (26, modeDataJ1M27)], (5800480350017194709/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b26 : entryChecks 1 bflatBlockJ1B26.entries = true := by
  simp only [entryChecks,bflatBlockJ1B26,List.all_cons,List.all_nil,
    mode_checked_j1_m27,Bool.and_self]
theorem block_mass_checked_j1_b26 : blockMassCheck bflatBlockJ1B26 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
