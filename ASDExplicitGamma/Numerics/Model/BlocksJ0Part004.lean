module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B4 : ModeBlockData :=
  ⟨⟨4, 5, (191824916536219698709/10000000000000000000000 : ℚ), (174528265655478568263/10000000000000000000000 : ℚ)⟩, [
    (4, modeDataJ0M5)], (47956229134054924677/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b4 : entryChecks 0 bflatBlockJ0B4.entries = true := by
  simp only [entryChecks,bflatBlockJ0B4,List.all_cons,List.all_nil,
    mode_checked_j0_m5,Bool.and_self]
theorem block_mass_checked_j0_b4 : blockMassCheck bflatBlockJ0B4 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
