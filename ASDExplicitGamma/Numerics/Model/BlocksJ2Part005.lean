module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B5 : ModeBlockData :=
  ⟨⟨5, 6, (302236522305417250687/5000000000000000000000 : ℚ), (26668522605447443721/10000000000000000000000 : ℚ)⟩, [
    (5, modeDataJ2M6)], (604473044610834501373/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b5 : entryChecks 2 bflatBlockJ2B5.entries = true := by
  simp only [entryChecks,bflatBlockJ2B5,List.all_cons,List.all_nil,
    mode_checked_j2_m6,Bool.and_self]
theorem block_mass_checked_j2_b5 : blockMassCheck bflatBlockJ2B5 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
