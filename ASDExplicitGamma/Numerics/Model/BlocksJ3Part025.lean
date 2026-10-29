module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B25 : ModeBlockData :=
  ⟨⟨25, 26, (21991646139348188939/1250000000000000000000 : ℚ), (2726908727769826083/10000000000000000000000 : ℚ)⟩, [
    (25, modeDataJ3M26)], (175933169114785511511/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b25 : entryChecks 3 bflatBlockJ3B25.entries = true := by
  simp only [entryChecks,bflatBlockJ3B25,List.all_cons,List.all_nil,
    mode_checked_j3_m26,Bool.and_self]
theorem block_mass_checked_j3_b25 : blockMassCheck bflatBlockJ3B25 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
