module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B47 : ModeBlockData :=
  ⟨⟨47, 48, (4990449311191881141/2000000000000000000000 : ℚ), (39247662004108949/10000000000000000000000 : ℚ)⟩, [
    (47, modeDataJ5M48)], (3119030819494925713/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b47 : entryChecks 5 bflatBlockJ5B47.entries = true := by
  simp only [entryChecks,bflatBlockJ5B47,List.all_cons,List.all_nil,
    mode_checked_j5_m48,Bool.and_self]
theorem block_mass_checked_j5_b47 : blockMassCheck bflatBlockJ5B47 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
