module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B35 : ModeBlockData :=
  ⟨⟨35, 36, (71675139424436118977/10000000000000000000000 : ℚ), (343628921271257449/10000000000000000000000 : ℚ)⟩, [
    (35, modeDataJ4M36)], (1119924053506814359/156250000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b35 : entryChecks 4 bflatBlockJ4B35.entries = true := by
  simp only [entryChecks,bflatBlockJ4B35,List.all_cons,List.all_nil,
    mode_checked_j4_m36,Bool.and_self]
theorem block_mass_checked_j4_b35 : blockMassCheck bflatBlockJ4B35 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
