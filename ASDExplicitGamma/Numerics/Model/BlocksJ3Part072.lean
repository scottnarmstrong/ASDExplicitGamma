module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B72 : ModeBlockData :=
  ⟨⟨80, 82, (27008051947989973473/10000000000000000000000 : ℚ), (15873743084180127/100000000000000000000 : ℚ)⟩, [
    (80, modeDataJ3M81),
    (81, modeDataJ3M82)], (27008051947989973471/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b72 : entryChecks 3 bflatBlockJ3B72.entries = true := by
  simp only [entryChecks,bflatBlockJ3B72,List.all_cons,List.all_nil,
    mode_checked_j3_m81,
    mode_checked_j3_m82,Bool.and_self]
theorem block_mass_checked_j3_b72 : blockMassCheck bflatBlockJ3B72 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
