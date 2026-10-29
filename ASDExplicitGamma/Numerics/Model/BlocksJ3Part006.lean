module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B6 : ModeBlockData :=
  ⟨⟨6, 7, (222873233847093975541/10000000000000000000000 : ℚ), (1581749956369702999/5000000000000000000000 : ℚ)⟩, [
    (6, modeDataJ3M7)], (11143661692354698777/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b6 : entryChecks 3 bflatBlockJ3B6.entries = true := by
  simp only [entryChecks,bflatBlockJ3B6,List.all_cons,List.all_nil,
    mode_checked_j3_m7,Bool.and_self]
theorem block_mass_checked_j3_b6 : blockMassCheck bflatBlockJ3B6 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
