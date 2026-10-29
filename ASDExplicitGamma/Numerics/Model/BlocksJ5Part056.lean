module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B56 : ModeBlockData :=
  ⟨⟨56, 57, (24842989907210871557/10000000000000000000000 : ℚ), (39138501384722643/10000000000000000000000 : ℚ)⟩, [
    (56, modeDataJ5M57)], (6210747476802717889/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b56 : entryChecks 5 bflatBlockJ5B56.entries = true := by
  simp only [entryChecks,bflatBlockJ5B56,List.all_cons,List.all_nil,
    mode_checked_j5_m57,Bool.and_self]
theorem block_mass_checked_j5_b56 : blockMassCheck bflatBlockJ5B56 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
