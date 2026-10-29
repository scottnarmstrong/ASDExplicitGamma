module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B46 : ModeBlockData :=
  ⟨⟨46, 47, (2415976797244262593/10000000000000000000000 : ℚ), (1961977237936175743/10000000000000000000000 : ℚ)⟩, [
    (46, modeDataJ2M47)], (37749637456941603/156250000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b46 : entryChecks 2 bflatBlockJ2B46.entries = true := by
  simp only [entryChecks,bflatBlockJ2B46,List.all_cons,List.all_nil,
    mode_checked_j2_m47,Bool.and_self]
theorem block_mass_checked_j2_b46 : blockMassCheck bflatBlockJ2B46 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
