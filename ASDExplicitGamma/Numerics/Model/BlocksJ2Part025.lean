module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B25 : ModeBlockData :=
  ⟨⟨25, 26, (7348473167632040181/1250000000000000000000 : ℚ), (7873993232990990227/10000000000000000000000 : ℚ)⟩, [
    (25, modeDataJ2M26)], (58787785341056321447/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b25 : entryChecks 2 bflatBlockJ2B25.entries = true := by
  simp only [entryChecks,bflatBlockJ2B25,List.all_cons,List.all_nil,
    mode_checked_j2_m26,Bool.and_self]
theorem block_mass_checked_j2_b25 : blockMassCheck bflatBlockJ2B25 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
