module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B35 : ModeBlockData :=
  ⟨⟨35, 36, (12534634230165045367/5000000000000000000000 : ℚ), (39364467382700913/10000000000000000000000 : ℚ)⟩, [
    (35, modeDataJ5M36)], (25069268460330090733/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b35 : entryChecks 5 bflatBlockJ5B35.entries = true := by
  simp only [entryChecks,bflatBlockJ5B35,List.all_cons,List.all_nil,
    mode_checked_j5_m36,Bool.and_self]
theorem block_mass_checked_j5_b35 : blockMassCheck bflatBlockJ5B35 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
