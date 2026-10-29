module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part011

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B108 : ModeBlockData :=
  ⟨⟨187, 191, (99930925969563787/2000000000000000000000 : ℚ), (233730580242583121/5000000000000000000000 : ℚ)⟩, [
    (187, modeDataJ3M188),
    (188, modeDataJ3M189),
    (189, modeDataJ3M190),
    (190, modeDataJ3M191)], (499654629847818931/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b108 : entryChecks 3 bflatBlockJ3B108.entries = true := by
  simp only [entryChecks,bflatBlockJ3B108,List.all_cons,List.all_nil,
    mode_checked_j3_m188,
    mode_checked_j3_m189,
    mode_checked_j3_m190,
    mode_checked_j3_m191,Bool.and_self]
theorem block_mass_checked_j3_b108 : blockMassCheck bflatBlockJ3B108 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
