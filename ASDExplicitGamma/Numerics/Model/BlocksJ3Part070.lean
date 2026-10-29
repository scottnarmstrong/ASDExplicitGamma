module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B70 : ModeBlockData :=
  ⟨⟨76, 78, (18373649769867389903/5000000000000000000000 : ℚ), (44361809169690919/250000000000000000000 : ℚ)⟩, [
    (76, modeDataJ3M77),
    (77, modeDataJ3M78)], (9186824884933694951/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b70 : entryChecks 3 bflatBlockJ3B70.entries = true := by
  simp only [entryChecks,bflatBlockJ3B70,List.all_cons,List.all_nil,
    mode_checked_j3_m77,
    mode_checked_j3_m78,Bool.and_self]
theorem block_mass_checked_j3_b70 : blockMassCheck bflatBlockJ3B70 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
