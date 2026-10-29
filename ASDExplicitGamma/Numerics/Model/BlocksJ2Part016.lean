module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B16 : ModeBlockData :=
  ⟨⟨16, 17, (63241784092810076579/2500000000000000000000 : ℚ), (15827057638528763459/10000000000000000000000 : ℚ)⟩, [
    (16, modeDataJ2M17)], (50593427274248061263/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b16 : entryChecks 2 bflatBlockJ2B16.entries = true := by
  simp only [entryChecks,bflatBlockJ2B16,List.all_cons,List.all_nil,
    mode_checked_j2_m17,Bool.and_self]
theorem block_mass_checked_j2_b16 : blockMassCheck bflatBlockJ2B16 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
