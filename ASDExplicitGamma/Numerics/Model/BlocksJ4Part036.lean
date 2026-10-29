module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B36 : ModeBlockData :=
  ⟨⟨36, 37, (8932049833412342257/1250000000000000000000 : ℚ), (342965901667221311/10000000000000000000000 : ℚ)⟩, [
    (36, modeDataJ4M37)], (14291279733459747611/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b36 : entryChecks 4 bflatBlockJ4B36.entries = true := by
  simp only [entryChecks,bflatBlockJ4B36,List.all_cons,List.all_nil,
    mode_checked_j4_m37,Bool.and_self]
theorem block_mass_checked_j4_b36 : blockMassCheck bflatBlockJ4B36 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
