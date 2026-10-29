module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B29 : ModeBlockData :=
  ⟨⟨29, 30, (7287238591513376227/1000000000000000000000 : ℚ), (347250177719084593/10000000000000000000000 : ℚ)⟩, [
    (29, modeDataJ4M30)], (72872385915133762269/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b29 : entryChecks 4 bflatBlockJ4B29.entries = true := by
  simp only [entryChecks,bflatBlockJ4B29,List.all_cons,List.all_nil,
    mode_checked_j4_m30,Bool.and_self]
theorem block_mass_checked_j4_b29 : blockMassCheck bflatBlockJ4B29 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
