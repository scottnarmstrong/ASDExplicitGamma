module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B26 : ModeBlockData :=
  ⟨⟨26, 27, (36697490713825652199/5000000000000000000000 : ℚ), (17441341204582289/500000000000000000000 : ℚ)⟩, [
    (26, modeDataJ4M27)], (73394981427651304397/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b26 : entryChecks 4 bflatBlockJ4B26.entries = true := by
  simp only [entryChecks,bflatBlockJ4B26,List.all_cons,List.all_nil,
    mode_checked_j4_m27,Bool.and_self]
theorem block_mass_checked_j4_b26 : blockMassCheck bflatBlockJ4B26 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
