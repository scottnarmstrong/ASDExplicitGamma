module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B19 : ModeBlockData :=
  ⟨⟨19, 20, (10213610346372881453/10000000000000000000000 : ℚ), (2543153130587550031/2500000000000000000000 : ℚ)⟩, [
    (19, modeDataJ0M20)], (2553402586593220363/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b19 : entryChecks 0 bflatBlockJ0B19.entries = true := by
  simp only [entryChecks,bflatBlockJ0B19,List.all_cons,List.all_nil,
    mode_checked_j0_m20,Bool.and_self]
theorem block_mass_checked_j0_b19 : blockMassCheck bflatBlockJ0B19 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
