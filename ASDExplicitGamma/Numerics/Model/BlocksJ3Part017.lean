module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B17 : ModeBlockData :=
  ⟨⟨17, 18, (201035735326903972101/10000000000000000000000 : ℚ), (2963169178383049303/10000000000000000000000 : ℚ)⟩, [
    (17, modeDataJ3M18)], (2010357353269039721/100000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b17 : entryChecks 3 bflatBlockJ3B17.entries = true := by
  simp only [entryChecks,bflatBlockJ3B17,List.all_cons,List.all_nil,
    mode_checked_j3_m18,Bool.and_self]
theorem block_mass_checked_j3_b17 : blockMassCheck bflatBlockJ3B17 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
