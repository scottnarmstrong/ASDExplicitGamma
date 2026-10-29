module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B3 : ModeBlockData :=
  ⟨⟨3, 4, (75610957052346391011/10000000000000000000000 : ℚ), (35548582625532191/1000000000000000000000 : ℚ)⟩, [
    (3, modeDataJ4M4)], (7561095705234639101/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b3 : entryChecks 4 bflatBlockJ4B3.entries = true := by
  simp only [entryChecks,bflatBlockJ4B3,List.all_cons,List.all_nil,
    mode_checked_j4_m4,Bool.and_self]
theorem block_mass_checked_j4_b3 : blockMassCheck bflatBlockJ4B3 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
