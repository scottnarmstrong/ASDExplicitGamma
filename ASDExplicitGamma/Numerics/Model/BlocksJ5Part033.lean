module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B33 : ModeBlockData :=
  ⟨⟨33, 34, (25085560916850549169/10000000000000000000000 : ℚ), (7876144082374273/2000000000000000000000 : ℚ)⟩, [
    (33, modeDataJ5M34)], (1567847557303159323/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b33 : entryChecks 5 bflatBlockJ5B33.entries = true := by
  simp only [entryChecks,bflatBlockJ5B33,List.all_cons,List.all_nil,
    mode_checked_j5_m34,Bool.and_self]
theorem block_mass_checked_j5_b33 : blockMassCheck bflatBlockJ5B33 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
