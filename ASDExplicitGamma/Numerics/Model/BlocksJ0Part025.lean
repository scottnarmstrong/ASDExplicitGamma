module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B25 : ModeBlockData :=
  ⟨⟨25, 26, (3011829771598356141/5000000000000000000000 : ℚ), (6009448218853613427/10000000000000000000000 : ℚ)⟩, [
    (25, modeDataJ0M26)], (6023659543196712281/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b25 : entryChecks 0 bflatBlockJ0B25.entries = true := by
  simp only [entryChecks,bflatBlockJ0B25,List.all_cons,List.all_nil,
    mode_checked_j0_m26,Bool.and_self]
theorem block_mass_checked_j0_b25 : blockMassCheck bflatBlockJ0B25 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
