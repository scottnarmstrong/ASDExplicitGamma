module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B14 : ModeBlockData :=
  ⟨⟨14, 15, (1259707546587519383/500000000000000000000 : ℚ), (39488989956372867/10000000000000000000000 : ℚ)⟩, [
    (14, modeDataJ5M15)], (25194150931750387659/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b14 : entryChecks 5 bflatBlockJ5B14.entries = true := by
  simp only [entryChecks,bflatBlockJ5B14,List.all_cons,List.all_nil,
    mode_checked_j5_m15,Bool.and_self]
theorem block_mass_checked_j5_b14 : blockMassCheck bflatBlockJ5B14 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
