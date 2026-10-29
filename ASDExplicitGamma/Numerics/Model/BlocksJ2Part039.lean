module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B39 : ModeBlockData :=
  ⟨⟨39, 40, (789728247879269/2441406250000000000 : ℚ), (2802722289815941983/10000000000000000000000 : ℚ)⟩, [
    (39, modeDataJ2M40)], (3234726903313485823/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b39 : entryChecks 2 bflatBlockJ2B39.entries = true := by
  simp only [entryChecks,bflatBlockJ2B39,List.all_cons,List.all_nil,
    mode_checked_j2_m40,Bool.and_self]
theorem block_mass_checked_j2_b39 : blockMassCheck bflatBlockJ2B39 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
