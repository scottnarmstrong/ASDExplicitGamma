module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B12 : ModeBlockData :=
  ⟨⟨12, 13, (21309109192226678129/1000000000000000000000 : ℚ), (307430884196835077/1000000000000000000000 : ℚ)⟩, [
    (12, modeDataJ3M13)], (213091091922266781289/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b12 : entryChecks 3 bflatBlockJ3B12.entries = true := by
  simp only [entryChecks,bflatBlockJ3B12,List.all_cons,List.all_nil,
    mode_checked_j3_m13,Bool.and_self]
theorem block_mass_checked_j3_b12 : blockMassCheck bflatBlockJ3B12 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
