module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B26 : ModeBlockData :=
  ⟨⟨26, 27, (2513531240329520119/1000000000000000000000 : ℚ), (492879218856823/125000000000000000000 : ℚ)⟩, [
    (26, modeDataJ5M27)], (25135312403295201189/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b26 : entryChecks 5 bflatBlockJ5B26.entries = true := by
  simp only [entryChecks,bflatBlockJ5B26,List.all_cons,List.all_nil,
    mode_checked_j5_m27,Bool.and_self]
theorem block_mass_checked_j5_b26 : blockMassCheck bflatBlockJ5B26 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
