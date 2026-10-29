module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B7 : ModeBlockData :=
  ⟨⟨7, 8, (75459884684217012133/10000000000000000000000 : ℚ), (355033193736819397/10000000000000000000000 : ℚ)⟩, [
    (7, modeDataJ4M8)], (18864971171054253033/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b7 : entryChecks 4 bflatBlockJ4B7.entries = true := by
  simp only [entryChecks,bflatBlockJ4B7,List.all_cons,List.all_nil,
    mode_checked_j4_m8,Bool.and_self]
theorem block_mass_checked_j4_b7 : blockMassCheck bflatBlockJ4B7 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
