module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B28 : ModeBlockData :=
  ⟨⟨28, 29, (625244878370283561/1250000000000000000000 : ℚ), (4904841712076322189/10000000000000000000000 : ℚ)⟩, [
    (28, modeDataJ1M29)], (5001959026962268487/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b28 : entryChecks 1 bflatBlockJ1B28.entries = true := by
  simp only [entryChecks,bflatBlockJ1B28,List.all_cons,List.all_nil,
    mode_checked_j1_m29,Bool.and_self]
theorem block_mass_checked_j1_b28 : blockMassCheck bflatBlockJ1B28 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
