module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B103 : ModeBlockData :=
  ⟨⟨167, 171, (325996270634621971/5000000000000000000000 : ℚ), (590325468191673793/10000000000000000000000 : ℚ)⟩, [
    (167, modeDataJ3M168),
    (168, modeDataJ3M169),
    (169, modeDataJ3M170),
    (170, modeDataJ3M171)], (325996270634621969/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b103 : entryChecks 3 bflatBlockJ3B103.entries = true := by
  simp only [entryChecks,bflatBlockJ3B103,List.all_cons,List.all_nil,
    mode_checked_j3_m168,
    mode_checked_j3_m169,
    mode_checked_j3_m170,
    mode_checked_j3_m171,Bool.and_self]
theorem block_mass_checked_j3_b103 : blockMassCheck bflatBlockJ3B103 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
