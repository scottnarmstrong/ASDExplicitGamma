module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B55 : ModeBlockData :=
  ⟨⟨55, 56, (65979008206656644077/10000000000000000000000 : ℚ), (156562680472896253/1000000000000000000000 : ℚ)⟩, [
    (55, modeDataJ3M56)], (16494752051664161019/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b55 : entryChecks 3 bflatBlockJ3B55.entries = true := by
  simp only [entryChecks,bflatBlockJ3B55,List.all_cons,List.all_nil,
    mode_checked_j3_m56,Bool.and_self]
theorem block_mass_checked_j3_b55 : blockMassCheck bflatBlockJ3B55 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
