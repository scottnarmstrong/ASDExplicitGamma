module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B33 : ModeBlockData :=
  ⟨⟨33, 34, (14419269517663981407/2000000000000000000000 : ℚ), (344904406234746271/10000000000000000000000 : ℚ)⟩, [
    (33, modeDataJ4M34)], (36048173794159953517/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b33 : entryChecks 4 bflatBlockJ4B33.entries = true := by
  simp only [entryChecks,bflatBlockJ4B33,List.all_cons,List.all_nil,
    mode_checked_j4_m34,Bool.and_self]
theorem block_mass_checked_j4_b33 : blockMassCheck bflatBlockJ4B33 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
