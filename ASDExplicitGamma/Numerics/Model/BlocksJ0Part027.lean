module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B27 : ModeBlockData :=
  ⟨⟨27, 28, (1297618819838992731/2500000000000000000000 : ℚ), (323745634919810319/625000000000000000000 : ℚ)⟩, [
    (27, modeDataJ0M28)], (5190475279355970923/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b27 : entryChecks 0 bflatBlockJ0B27.entries = true := by
  simp only [entryChecks,bflatBlockJ0B27,List.all_cons,List.all_nil,
    mode_checked_j0_m28,Bool.and_self]
theorem block_mass_checked_j0_b27 : blockMassCheck bflatBlockJ0B27 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
