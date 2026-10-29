module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B76 : ModeBlockData :=
  ⟨⟨88, 90, (1680337386379807383/1250000000000000000000 : ℚ), (127339647376579607/1000000000000000000000 : ℚ)⟩, [
    (88, modeDataJ3M89),
    (89, modeDataJ3M90)], (6721349545519229531/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b76 : entryChecks 3 bflatBlockJ3B76.entries = true := by
  simp only [entryChecks,bflatBlockJ3B76,List.all_cons,List.all_nil,
    mode_checked_j3_m89,
    mode_checked_j3_m90,Bool.and_self]
theorem block_mass_checked_j3_b76 : blockMassCheck bflatBlockJ3B76 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
