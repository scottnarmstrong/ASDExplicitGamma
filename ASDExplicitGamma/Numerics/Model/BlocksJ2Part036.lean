module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B36 : ModeBlockData :=
  ⟨⟨36, 37, (4637056239254810213/10000000000000000000000 : ℚ), (421200733003292707/1250000000000000000000 : ℚ)⟩, [
    (36, modeDataJ2M37)], (1159264059813702553/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b36 : entryChecks 2 bflatBlockJ2B36.entries = true := by
  simp only [entryChecks,bflatBlockJ2B36,List.all_cons,List.all_nil,
    mode_checked_j2_m37,Bool.and_self]
theorem block_mass_checked_j2_b36 : blockMassCheck bflatBlockJ2B36 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
