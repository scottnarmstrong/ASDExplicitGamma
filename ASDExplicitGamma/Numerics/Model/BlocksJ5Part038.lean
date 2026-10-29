module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B38 : ModeBlockData :=
  ⟨⟨38, 39, (12521552157725545071/5000000000000000000000 : ℚ), (39338361815738041/10000000000000000000000 : ℚ)⟩, [
    (38, modeDataJ5M39)], (25043104315451090141/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b38 : entryChecks 5 bflatBlockJ5B38.entries = true := by
  simp only [entryChecks,bflatBlockJ5B38,List.all_cons,List.all_nil,
    mode_checked_j5_m39,Bool.and_self]
theorem block_mass_checked_j5_b38 : blockMassCheck bflatBlockJ5B38 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
