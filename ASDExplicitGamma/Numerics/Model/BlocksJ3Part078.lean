module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B78 : ModeBlockData :=
  ⟨⟨92, 94, (4533942916843431377/5000000000000000000000 : ℚ), (572037858709928631/5000000000000000000000 : ℚ)⟩, [
    (92, modeDataJ3M93),
    (93, modeDataJ3M94)], (283371432302714461/312500000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b78 : entryChecks 3 bflatBlockJ3B78.entries = true := by
  simp only [entryChecks,bflatBlockJ3B78,List.all_cons,List.all_nil,
    mode_checked_j3_m93,
    mode_checked_j3_m94,Bool.and_self]
theorem block_mass_checked_j3_b78 : blockMassCheck bflatBlockJ3B78 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
