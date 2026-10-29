module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B46 : ModeBlockData :=
  ⟨⟨46, 47, (24963254164359429257/10000000000000000000000 : ℚ), (39258654243263429/10000000000000000000000 : ℚ)⟩, [
    (46, modeDataJ5M47)], (3120406770544928657/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b46 : entryChecks 5 bflatBlockJ5B46.entries = true := by
  simp only [entryChecks,bflatBlockJ5B46,List.all_cons,List.all_nil,
    mode_checked_j5_m47,Bool.and_self]
theorem block_mass_checked_j5_b46 : blockMassCheck bflatBlockJ5B46 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
