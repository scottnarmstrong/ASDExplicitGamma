module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B23 : ModeBlockData :=
  ⟨⟨23, 24, (5030632174964076891/2000000000000000000000 : ℚ), (19724066318712189/5000000000000000000000 : ℚ)⟩, [
    (23, modeDataJ5M24)], (12576580437410192227/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b23 : entryChecks 5 bflatBlockJ5B23.entries = true := by
  simp only [entryChecks,bflatBlockJ5B23,List.all_cons,List.all_nil,
    mode_checked_j5_m24,Bool.and_self]
theorem block_mass_checked_j5_b23 : blockMassCheck bflatBlockJ5B23 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
