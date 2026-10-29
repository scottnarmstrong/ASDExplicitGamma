module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B42 : ModeBlockData :=
  ⟨⟨42, 43, (12502503646698444359/5000000000000000000000 : ℚ), (7860067925665569/2000000000000000000000 : ℚ)⟩, [
    (42, modeDataJ5M43)], (25005007293396888717/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b42 : entryChecks 5 bflatBlockJ5B42.entries = true := by
  simp only [entryChecks,bflatBlockJ5B42,List.all_cons,List.all_nil,
    mode_checked_j5_m43,Bool.and_self]
theorem block_mass_checked_j5_b42 : blockMassCheck bflatBlockJ5B42 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
