module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B47 : ModeBlockData :=
  ⟨⟨47, 48, (46438977424693078433/5000000000000000000000 : ℚ), (938982008172683249/5000000000000000000000 : ℚ)⟩, [
    (47, modeDataJ3M48)], (18575590969877231373/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b47 : entryChecks 3 bflatBlockJ3B47.entries = true := by
  simp only [entryChecks,bflatBlockJ3B47,List.all_cons,List.all_nil,
    mode_checked_j3_m48,Bool.and_self]
theorem block_mass_checked_j3_b47 : blockMassCheck bflatBlockJ3B47 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
