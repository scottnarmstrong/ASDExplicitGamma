module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B6 : ModeBlockData :=
  ⟨⟨6, 7, (89057537962729211087/10000000000000000000000 : ℚ), (21413417914788796439/2500000000000000000000 : ℚ)⟩, [
    (6, modeDataJ0M7)], (44528768981364605543/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b6 : entryChecks 0 bflatBlockJ0B6.entries = true := by
  simp only [entryChecks,bflatBlockJ0B6,List.all_cons,List.all_nil,
    mode_checked_j0_m7,Bool.and_self]
theorem block_mass_checked_j0_b6 : blockMassCheck bflatBlockJ0B6 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
