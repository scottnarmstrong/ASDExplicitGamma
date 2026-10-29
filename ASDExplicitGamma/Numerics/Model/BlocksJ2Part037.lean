module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B37 : ModeBlockData :=
  ⟨⟨37, 38, (795389932209616137/2000000000000000000000 : ℚ), (49388943912696493/156250000000000000000 : ℚ)⟩, [
    (37, modeDataJ2M38)], (994237415262020171/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b37 : entryChecks 2 bflatBlockJ2B37.entries = true := by
  simp only [entryChecks,bflatBlockJ2B37,List.all_cons,List.all_nil,
    mode_checked_j2_m38,Bool.and_self]
theorem block_mass_checked_j2_b37 : blockMassCheck bflatBlockJ2B37 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
