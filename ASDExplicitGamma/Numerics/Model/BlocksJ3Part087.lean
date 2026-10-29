module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B87 : ModeBlockData :=
  ⟨⟨115, 118, (606354608785665597/5000000000000000000000 : ℚ), (198228088849207129/2000000000000000000000 : ℚ)⟩, [
    (115, modeDataJ3M116),
    (116, modeDataJ3M117),
    (117, modeDataJ3M118)], (1212709217571331191/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b87 : entryChecks 3 bflatBlockJ3B87.entries = true := by
  simp only [entryChecks,bflatBlockJ3B87,List.all_cons,List.all_nil,
    mode_checked_j3_m116,
    mode_checked_j3_m117,
    mode_checked_j3_m118,Bool.and_self]
theorem block_mass_checked_j3_b87 : blockMassCheck bflatBlockJ3B87 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
