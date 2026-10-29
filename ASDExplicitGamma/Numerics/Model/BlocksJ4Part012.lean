module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B12 : ModeBlockData :=
  ⟨⟨12, 13, (75130371403935910241/10000000000000000000000 : ℚ), (88511314085410591/2500000000000000000000 : ℚ)⟩, [
    (12, modeDataJ4M13)], (469564821274599439/62500000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b12 : entryChecks 4 bflatBlockJ4B12.entries = true := by
  simp only [entryChecks,bflatBlockJ4B12,List.all_cons,List.all_nil,
    mode_checked_j4_m13,Bool.and_self]
theorem block_mass_checked_j4_b12 : blockMassCheck bflatBlockJ4B12 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
