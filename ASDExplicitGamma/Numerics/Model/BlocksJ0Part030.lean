module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B30 : ModeBlockData :=
  ⟨⟨30, 31, (528911834534717651/1250000000000000000000 : ℚ), (4224291885980755639/10000000000000000000000 : ℚ)⟩, [
    (30, modeDataJ0M31)], (4231294676277741207/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b30 : entryChecks 0 bflatBlockJ0B30.entries = true := by
  simp only [entryChecks,bflatBlockJ0B30,List.all_cons,List.all_nil,
    mode_checked_j0_m31,Bool.and_self]
theorem block_mass_checked_j0_b30 : blockMassCheck bflatBlockJ0B30 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
