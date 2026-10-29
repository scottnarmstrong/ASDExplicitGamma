module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B82 : ModeBlockData :=
  ⟨⟨100, 103, (2678057181131975703/5000000000000000000000 : ℚ), (691368066523872789/5000000000000000000000 : ℚ)⟩, [
    (100, modeDataJ3M101),
    (101, modeDataJ3M102),
    (102, modeDataJ3M103)], (5356114362263951403/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b82 : entryChecks 3 bflatBlockJ3B82.entries = true := by
  simp only [entryChecks,bflatBlockJ3B82,List.all_cons,List.all_nil,
    mode_checked_j3_m101,
    mode_checked_j3_m102,
    mode_checked_j3_m103,Bool.and_self]
theorem block_mass_checked_j3_b82 : blockMassCheck bflatBlockJ3B82 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
