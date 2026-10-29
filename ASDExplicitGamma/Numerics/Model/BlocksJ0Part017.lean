module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B17 : ModeBlockData :=
  ⟨⟨17, 18, (12633537421517680217/10000000000000000000000 : ℚ), (12570675823689577733/10000000000000000000000 : ℚ)⟩, [
    (17, modeDataJ0M18)], (1579192177689710027/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b17 : entryChecks 0 bflatBlockJ0B17.entries = true := by
  simp only [entryChecks,bflatBlockJ0B17,List.all_cons,List.all_nil,
    mode_checked_j0_m18,Bool.and_self]
theorem block_mass_checked_j0_b17 : blockMassCheck bflatBlockJ0B17 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
