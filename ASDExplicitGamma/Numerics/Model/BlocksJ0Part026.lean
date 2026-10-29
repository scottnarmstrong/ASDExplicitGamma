module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B26 : ModeBlockData :=
  ⟨⟨26, 27, (5583797280830046029/10000000000000000000000 : ℚ), (5571589963467224329/10000000000000000000000 : ℚ)⟩, [
    (26, modeDataJ0M27)], (1395949320207511507/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b26 : entryChecks 0 bflatBlockJ0B26.entries = true := by
  simp only [entryChecks,bflatBlockJ0B26,List.all_cons,List.all_nil,
    mode_checked_j0_m27,Bool.and_self]
theorem block_mass_checked_j0_b26 : blockMassCheck bflatBlockJ0B26 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
