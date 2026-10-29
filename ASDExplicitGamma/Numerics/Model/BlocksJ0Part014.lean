module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B14 : ModeBlockData :=
  ⟨⟨14, 15, (9136990487992231851/5000000000000000000000 : ℚ), (18141793982573317991/10000000000000000000000 : ℚ)⟩, [
    (14, modeDataJ0M15)], (18273980975984463701/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b14 : entryChecks 0 bflatBlockJ0B14.entries = true := by
  simp only [entryChecks,bflatBlockJ0B14,List.all_cons,List.all_nil,
    mode_checked_j0_m15,Bool.and_self]
theorem block_mass_checked_j0_b14 : blockMassCheck bflatBlockJ0B14 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
