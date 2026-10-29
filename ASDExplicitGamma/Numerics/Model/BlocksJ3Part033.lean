module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B33 : ModeBlockData :=
  ⟨⟨33, 34, (146294185252037108907/10000000000000000000000 : ℚ), (60947970564464517/250000000000000000000 : ℚ)⟩, [
    (33, modeDataJ3M34)], (73147092626018554453/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b33 : entryChecks 3 bflatBlockJ3B33.entries = true := by
  simp only [entryChecks,bflatBlockJ3B33,List.all_cons,List.all_nil,
    mode_checked_j3_m34,Bool.and_self]
theorem block_mass_checked_j3_b33 : blockMassCheck bflatBlockJ3B33 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
