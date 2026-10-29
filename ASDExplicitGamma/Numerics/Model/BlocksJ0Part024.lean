module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B24 : ModeBlockData :=
  ⟨⟨24, 25, (1629429464482526917/2500000000000000000000 : ℚ), (3250536840443447903/5000000000000000000000 : ℚ)⟩, [
    (24, modeDataJ0M25)], (6517717857930107667/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b24 : entryChecks 0 bflatBlockJ0B24.entries = true := by
  simp only [entryChecks,bflatBlockJ0B24,List.all_cons,List.all_nil,
    mode_checked_j0_m25,Bool.and_self]
theorem block_mass_checked_j0_b24 : blockMassCheck bflatBlockJ0B24 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
