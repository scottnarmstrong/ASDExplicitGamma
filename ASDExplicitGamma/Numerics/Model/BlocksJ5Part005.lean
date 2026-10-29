module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B5 : ModeBlockData :=
  ⟨⟨5, 6, (25216247656013528229/10000000000000000000000 : ℚ), (39511009218917307/10000000000000000000000 : ℚ)⟩, [
    (5, modeDataJ5M6)], (6304061914003382057/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b5 : entryChecks 5 bflatBlockJ5B5.entries = true := by
  simp only [entryChecks,bflatBlockJ5B5,List.all_cons,List.all_nil,
    mode_checked_j5_m6,Bool.and_self]
theorem block_mass_checked_j5_b5 : blockMassCheck bflatBlockJ5B5 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
