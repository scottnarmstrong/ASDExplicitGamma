module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B10 : ModeBlockData :=
  ⟨⟨10, 11, (4303305700818227611/1250000000000000000000 : ℚ), (33949317293905145591/10000000000000000000000 : ℚ)⟩, [
    (10, modeDataJ0M11)], (34426445606545820887/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b10 : entryChecks 0 bflatBlockJ0B10.entries = true := by
  simp only [entryChecks,bflatBlockJ0B10,List.all_cons,List.all_nil,
    mode_checked_j0_m11,Bool.and_self]
theorem block_mass_checked_j0_b10 : blockMassCheck bflatBlockJ0B10 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
