module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B23 : ModeBlockData :=
  ⟨⟨23, 24, (87006645372028757361/10000000000000000000000 : ℚ), (1162149609249632647/1250000000000000000000 : ℚ)⟩, [
    (23, modeDataJ2M24)], (1087583067150359467/125000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b23 : entryChecks 2 bflatBlockJ2B23.entries = true := by
  simp only [entryChecks,bflatBlockJ2B23,List.all_cons,List.all_nil,
    mode_checked_j2_m24,Bool.and_self]
theorem block_mass_checked_j2_b23 : blockMassCheck bflatBlockJ2B23 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
