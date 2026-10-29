module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B48 : ModeBlockData :=
  ⟨⟨48, 49, (89299377910246801131/10000000000000000000000 : ℚ), (229742309320995723/1250000000000000000000 : ℚ)⟩, [
    (48, modeDataJ3M49)], (8929937791024680113/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b48 : entryChecks 3 bflatBlockJ3B48.entries = true := by
  simp only [entryChecks,bflatBlockJ3B48,List.all_cons,List.all_nil,
    mode_checked_j3_m49,Bool.and_self]
theorem block_mass_checked_j3_b48 : blockMassCheck bflatBlockJ3B48 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
