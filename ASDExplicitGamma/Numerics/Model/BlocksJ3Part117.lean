module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part014

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B117 : ModeBlockData :=
  ⟨⟨229, 234, (197552323589078779/5000000000000000000000 : ℚ), (15405960834624369/400000000000000000000 : ℚ)⟩, [
    (229, modeDataJ3M230),
    (230, modeDataJ3M231),
    (231, modeDataJ3M232),
    (232, modeDataJ3M233),
    (233, modeDataJ3M234)], (395104647178157553/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b117 : entryChecks 3 bflatBlockJ3B117.entries = true := by
  simp only [entryChecks,bflatBlockJ3B117,List.all_cons,List.all_nil,
    mode_checked_j3_m230,
    mode_checked_j3_m231,
    mode_checked_j3_m232,
    mode_checked_j3_m233,
    mode_checked_j3_m234,Bool.and_self]
theorem block_mass_checked_j3_b117 : blockMassCheck bflatBlockJ3B117 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
