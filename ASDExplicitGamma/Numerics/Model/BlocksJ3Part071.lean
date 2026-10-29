module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B71 : ModeBlockData :=
  ⟨⟨78, 80, (31604060435124192999/10000000000000000000000 : ℚ), (104894863340817547/625000000000000000000 : ℚ)⟩, [
    (78, modeDataJ3M79),
    (79, modeDataJ3M80)], (31604060435124192997/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b71 : entryChecks 3 bflatBlockJ3B71.entries = true := by
  simp only [entryChecks,bflatBlockJ3B71,List.all_cons,List.all_nil,
    mode_checked_j3_m79,
    mode_checked_j3_m80,Bool.and_self]
theorem block_mass_checked_j3_b71 : blockMassCheck bflatBlockJ3B71 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
