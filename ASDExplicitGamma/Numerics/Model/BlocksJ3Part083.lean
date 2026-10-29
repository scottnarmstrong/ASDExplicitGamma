module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B83 : ModeBlockData :=
  ⟨⟨103, 106, (754465843140901363/2000000000000000000000 : ℚ), (160865510499219989/1250000000000000000000 : ℚ)⟩, [
    (103, modeDataJ3M104),
    (104, modeDataJ3M105),
    (105, modeDataJ3M106)], (943082303926126703/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b83 : entryChecks 3 bflatBlockJ3B83.entries = true := by
  simp only [entryChecks,bflatBlockJ3B83,List.all_cons,List.all_nil,
    mode_checked_j3_m104,
    mode_checked_j3_m105,
    mode_checked_j3_m106,Bool.and_self]
theorem block_mass_checked_j3_b83 : blockMassCheck bflatBlockJ3B83 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
