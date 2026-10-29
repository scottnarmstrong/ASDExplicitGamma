module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B8 : ModeBlockData :=
  ⟨⟨8, 9, (191762704300709081297/10000000000000000000000 : ℚ), (65183364201665264671/10000000000000000000000 : ℚ)⟩, [
    (8, modeDataJ1M9)], (11985169018794317581/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b8 : entryChecks 1 bflatBlockJ1B8.entries = true := by
  simp only [entryChecks,bflatBlockJ1B8,List.all_cons,List.all_nil,
    mode_checked_j1_m9,Bool.and_self]
theorem block_mass_checked_j1_b8 : blockMassCheck bflatBlockJ1B8 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
