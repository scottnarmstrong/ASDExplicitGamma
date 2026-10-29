module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B25 : ModeBlockData :=
  ⟨⟨25, 26, (36778823223369073247/5000000000000000000000 : ℚ), (174658541932513943/5000000000000000000000 : ℚ)⟩, [
    (25, modeDataJ4M26)], (73557646446738146493/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b25 : entryChecks 4 bflatBlockJ4B25.entries = true := by
  simp only [entryChecks,bflatBlockJ4B25,List.all_cons,List.all_nil,
    mode_checked_j4_m26,Bool.and_self]
theorem block_mass_checked_j4_b25 : blockMassCheck bflatBlockJ4B25 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
