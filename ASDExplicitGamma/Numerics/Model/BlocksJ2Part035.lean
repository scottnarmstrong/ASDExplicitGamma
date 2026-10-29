module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B35 : ModeBlockData :=
  ⟨⟨35, 36, (2795031077707848161/5000000000000000000000 : ℚ), (3601576112465554529/10000000000000000000000 : ℚ)⟩, [
    (35, modeDataJ2M36)], (5590062155415696321/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b35 : entryChecks 2 bflatBlockJ2B35.entries = true := by
  simp only [entryChecks,bflatBlockJ2B35,List.all_cons,List.all_nil,
    mode_checked_j2_m36,Bool.and_self]
theorem block_mass_checked_j2_b35 : blockMassCheck bflatBlockJ2B35 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
