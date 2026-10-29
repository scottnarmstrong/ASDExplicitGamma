module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B86 : ModeBlockData :=
  ⟨⟨112, 115, (184520076139268557/1250000000000000000000 : ℚ), (263471143616199733/2500000000000000000000 : ℚ)⟩, [
    (112, modeDataJ3M113),
    (113, modeDataJ3M114),
    (114, modeDataJ3M115)], (1476160609114148453/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b86 : entryChecks 3 bflatBlockJ3B86.entries = true := by
  simp only [entryChecks,bflatBlockJ3B86,List.all_cons,List.all_nil,
    mode_checked_j3_m113,
    mode_checked_j3_m114,
    mode_checked_j3_m115,Bool.and_self]
theorem block_mass_checked_j3_b86 : blockMassCheck bflatBlockJ3B86 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
