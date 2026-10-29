module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B98 : ModeBlockData :=
  ⟨⟨148, 151, (850792287733101961/10000000000000000000000 : ℚ), (22931313954202151/400000000000000000000 : ℚ)⟩, [
    (148, modeDataJ3M149),
    (149, modeDataJ3M150),
    (150, modeDataJ3M151)], (425396143866550979/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b98 : entryChecks 3 bflatBlockJ3B98.entries = true := by
  simp only [entryChecks,bflatBlockJ3B98,List.all_cons,List.all_nil,
    mode_checked_j3_m149,
    mode_checked_j3_m150,
    mode_checked_j3_m151,Bool.and_self]
theorem block_mass_checked_j3_b98 : blockMassCheck bflatBlockJ3B98 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
