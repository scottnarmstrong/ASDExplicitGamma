module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B27 : ModeBlockData :=
  ⟨⟨27, 28, (38124231561483505273/10000000000000000000000 : ℚ), (1332645353955359353/2000000000000000000000 : ℚ)⟩, [
    (27, modeDataJ2M28)], (4765528945185438159/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b27 : entryChecks 2 bflatBlockJ2B27.entries = true := by
  simp only [entryChecks,bflatBlockJ2B27,List.all_cons,List.all_nil,
    mode_checked_j2_m28,Bool.and_self]
theorem block_mass_checked_j2_b27 : blockMassCheck bflatBlockJ2B27 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
