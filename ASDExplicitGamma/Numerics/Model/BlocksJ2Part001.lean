module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B1 : ModeBlockData :=
  ⟨⟨1, 2, (672035237621951116621/10000000000000000000000 : ℚ), (3569997704367007389/1250000000000000000000 : ℚ)⟩, [
    (1, modeDataJ2M2)], (33601761881097555831/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b1 : entryChecks 2 bflatBlockJ2B1.entries = true := by
  simp only [entryChecks,bflatBlockJ2B1,List.all_cons,List.all_nil,
    mode_checked_j2_m2,Bool.and_self]
theorem block_mass_checked_j2_b1 : blockMassCheck bflatBlockJ2B1 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
