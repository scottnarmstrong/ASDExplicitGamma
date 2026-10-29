module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B102 : ModeBlockData :=
  ⟨⟨163, 167, (9021209145969287/125000000000000000000 : ℚ), (310405239499819827/5000000000000000000000 : ℚ)⟩, [
    (163, modeDataJ3M164),
    (164, modeDataJ3M165),
    (165, modeDataJ3M166),
    (166, modeDataJ3M167)], (180424182919385739/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b102 : entryChecks 3 bflatBlockJ3B102.entries = true := by
  simp only [entryChecks,bflatBlockJ3B102,List.all_cons,List.all_nil,
    mode_checked_j3_m164,
    mode_checked_j3_m165,
    mode_checked_j3_m166,
    mode_checked_j3_m167,Bool.and_self]
theorem block_mass_checked_j3_b102 : blockMassCheck bflatBlockJ3B102 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
