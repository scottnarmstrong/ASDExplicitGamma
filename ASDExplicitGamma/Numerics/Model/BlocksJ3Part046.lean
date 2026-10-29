module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B46 : ModeBlockData :=
  ⟨⟨46, 47, (48254009311080660547/5000000000000000000000 : ℚ), (1918165458605924711/10000000000000000000000 : ℚ)⟩, [
    (46, modeDataJ3M47)], (96508018622161321093/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b46 : entryChecks 3 bflatBlockJ3B46.entries = true := by
  simp only [entryChecks,bflatBlockJ3B46,List.all_cons,List.all_nil,
    mode_checked_j3_m47,Bool.and_self]
theorem block_mass_checked_j3_b46 : blockMassCheck bflatBlockJ3B46 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
