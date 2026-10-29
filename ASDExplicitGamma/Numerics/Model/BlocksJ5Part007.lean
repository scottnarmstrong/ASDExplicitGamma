module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B7 : ModeBlockData :=
  ⟨⟨7, 8, (25212972955397177749/10000000000000000000000 : ℚ), (39507746258849697/10000000000000000000000 : ℚ)⟩, [
    (7, modeDataJ5M8)], (6303243238849294437/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b7 : entryChecks 5 bflatBlockJ5B7.entries = true := by
  simp only [entryChecks,bflatBlockJ5B7,List.all_cons,List.all_nil,
    mode_checked_j5_m8,Bool.and_self]
theorem block_mass_checked_j5_b7 : blockMassCheck bflatBlockJ5B7 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
