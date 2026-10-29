module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B93 : ModeBlockData :=
  ⟨⟨133, 136, (105707690826754733/1000000000000000000000 : ℚ), (718324186942995207/10000000000000000000000 : ℚ)⟩, [
    (133, modeDataJ3M134),
    (134, modeDataJ3M135),
    (135, modeDataJ3M136)], (1057076908267547327/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b93 : entryChecks 3 bflatBlockJ3B93.entries = true := by
  simp only [entryChecks,bflatBlockJ3B93,List.all_cons,List.all_nil,
    mode_checked_j3_m134,
    mode_checked_j3_m135,
    mode_checked_j3_m136,Bool.and_self]
theorem block_mass_checked_j3_b93 : blockMassCheck bflatBlockJ3B93 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
