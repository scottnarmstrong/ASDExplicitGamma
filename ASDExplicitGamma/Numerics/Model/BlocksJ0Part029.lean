module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B29 : ModeBlockData :=
  ⟨⟨29, 30, (1129775369461684417/2500000000000000000000 : ℚ), (4511111905499182903/10000000000000000000000 : ℚ)⟩, [
    (29, modeDataJ0M30)], (4519101477846737667/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b29 : entryChecks 0 bflatBlockJ0B29.entries = true := by
  simp only [entryChecks,bflatBlockJ0B29,List.all_cons,List.all_nil,
    mode_checked_j0_m30,Bool.and_self]
theorem block_mass_checked_j0_b29 : blockMassCheck bflatBlockJ0B29 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
