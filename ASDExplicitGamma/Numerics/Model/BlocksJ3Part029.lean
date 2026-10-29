module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B29 : ModeBlockData :=
  ⟨⟨29, 30, (16148191229234013429/1000000000000000000000 : ℚ), (2587515850117923769/10000000000000000000000 : ℚ)⟩, [
    (29, modeDataJ3M30)], (161481912292340134289/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b29 : entryChecks 3 bflatBlockJ3B29.entries = true := by
  simp only [entryChecks,bflatBlockJ3B29,List.all_cons,List.all_nil,
    mode_checked_j3_m30,Bool.and_self]
theorem block_mass_checked_j3_b29 : blockMassCheck bflatBlockJ3B29 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
