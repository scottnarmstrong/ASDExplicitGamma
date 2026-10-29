module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B3 : ModeBlockData :=
  ⟨⟨3, 4, (259551735926608561139/2000000000000000000000 : ℚ), (191181005718590733863/10000000000000000000000 : ℚ)⟩, [
    (3, modeDataJ1M4)], (648879339816521402847/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b3 : entryChecks 1 bflatBlockJ1B3.entries = true := by
  simp only [entryChecks,bflatBlockJ1B3,List.all_cons,List.all_nil,
    mode_checked_j1_m4,Bool.and_self]
theorem block_mass_checked_j1_b3 : blockMassCheck bflatBlockJ1B3 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
