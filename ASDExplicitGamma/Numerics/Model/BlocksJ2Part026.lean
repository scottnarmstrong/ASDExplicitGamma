module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B26 : ModeBlockData :=
  ⟨⟨26, 27, (23791342126317381989/5000000000000000000000 : ℚ), (7242596022407251631/10000000000000000000000 : ℚ)⟩, [
    (26, modeDataJ2M27)], (47582684252634763977/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b26 : entryChecks 2 bflatBlockJ2B26.entries = true := by
  simp only [entryChecks,bflatBlockJ2B26,List.all_cons,List.all_nil,
    mode_checked_j2_m27,Bool.and_self]
theorem block_mass_checked_j2_b26 : blockMassCheck bflatBlockJ2B26 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
