module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B13 : ModeBlockData :=
  ⟨⟨13, 14, (1051204064091538437/500000000000000000000 : ℚ), (20848529435018219631/10000000000000000000000 : ℚ)⟩, [
    (13, modeDataJ0M14)], (21024081281830768739/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b13 : entryChecks 0 bflatBlockJ0B13.entries = true := by
  simp only [entryChecks,bflatBlockJ0B13,List.all_cons,List.all_nil,
    mode_checked_j0_m14,Bool.and_self]
theorem block_mass_checked_j0_b13 : blockMassCheck bflatBlockJ0B13 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
