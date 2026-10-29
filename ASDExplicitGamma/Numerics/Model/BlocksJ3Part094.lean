module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B94 : ModeBlockData :=
  ⟨⟨136, 139, (1044280068619994873/10000000000000000000000 : ℚ), (85624074259613487/1250000000000000000000 : ℚ)⟩, [
    (136, modeDataJ3M137),
    (137, modeDataJ3M138),
    (138, modeDataJ3M139)], (104428006861999487/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b94 : entryChecks 3 bflatBlockJ3B94.entries = true := by
  simp only [entryChecks,bflatBlockJ3B94,List.all_cons,List.all_nil,
    mode_checked_j3_m137,
    mode_checked_j3_m138,
    mode_checked_j3_m139,Bool.and_self]
theorem block_mass_checked_j3_b94 : blockMassCheck bflatBlockJ3B94 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
