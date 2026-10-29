module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B38 : ModeBlockData :=
  ⟨⟨38, 39, (353090647614101189/1000000000000000000000 : ℚ), (1486375577444526191/5000000000000000000000 : ℚ)⟩, [
    (38, modeDataJ2M39)], (3530906476141011889/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b38 : entryChecks 2 bflatBlockJ2B38.entries = true := by
  simp only [entryChecks,bflatBlockJ2B38,List.all_cons,List.all_nil,
    mode_checked_j2_m39,Bool.and_self]
theorem block_mass_checked_j2_b38 : blockMassCheck bflatBlockJ2B38 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
