module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B36 : ModeBlockData :=
  ⟨⟨36, 37, (16832530653409502851/1250000000000000000000 : ℚ), (92835328870284613/400000000000000000000 : ℚ)⟩, [
    (36, modeDataJ3M37)], (134660245227276022807/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b36 : entryChecks 3 bflatBlockJ3B36.entries = true := by
  simp only [entryChecks,bflatBlockJ3B36,List.all_cons,List.all_nil,
    mode_checked_j3_m37,Bool.and_self]
theorem block_mass_checked_j3_b36 : blockMassCheck bflatBlockJ3B36 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
