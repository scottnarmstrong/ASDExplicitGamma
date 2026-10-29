module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B20 : ModeBlockData :=
  ⟨⟨20, 21, (1851411415608138939/2000000000000000000000 : ℚ), (4611704226862365777/5000000000000000000000 : ℚ)⟩, [
    (20, modeDataJ0M21)], (4628528539020347347/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b20 : entryChecks 0 bflatBlockJ0B20.entries = true := by
  simp only [entryChecks,bflatBlockJ0B20,List.all_cons,List.all_nil,
    mode_checked_j0_m21,Bool.and_self]
theorem block_mass_checked_j0_b20 : blockMassCheck bflatBlockJ0B20 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
