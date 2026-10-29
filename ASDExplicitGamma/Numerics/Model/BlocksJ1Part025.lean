module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B25 : ModeBlockData :=
  ⟨⟨25, 26, (1569303554219033937/2500000000000000000000 : ℚ), (766242085026064211/1250000000000000000000 : ℚ)⟩, [
    (25, modeDataJ1M26)], (6277214216876135747/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b25 : entryChecks 1 bflatBlockJ1B25.entries = true := by
  simp only [entryChecks,bflatBlockJ1B25,List.all_cons,List.all_nil,
    mode_checked_j1_m26,Bool.and_self]
theorem block_mass_checked_j1_b25 : blockMassCheck bflatBlockJ1B25 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
