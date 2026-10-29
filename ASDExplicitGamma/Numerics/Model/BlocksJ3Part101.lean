module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part009
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B101 : ModeBlockData :=
  ⟨⟨159, 163, (202452746258451869/2500000000000000000000 : ℚ), (163433601278813759/2500000000000000000000 : ℚ)⟩, [
    (159, modeDataJ3M160),
    (160, modeDataJ3M161),
    (161, modeDataJ3M162),
    (162, modeDataJ3M163)], (50613186564612967/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b101 : entryChecks 3 bflatBlockJ3B101.entries = true := by
  simp only [entryChecks,bflatBlockJ3B101,List.all_cons,List.all_nil,
    mode_checked_j3_m160,
    mode_checked_j3_m161,
    mode_checked_j3_m162,
    mode_checked_j3_m163,Bool.and_self]
theorem block_mass_checked_j3_b101 : blockMassCheck bflatBlockJ3B101 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
