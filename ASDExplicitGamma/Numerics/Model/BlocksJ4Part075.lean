module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B75 : ModeBlockData :=
  ⟨⟨118, 124, (60260653379629049167/2500000000000000000000 : ℚ), (90874417203524811/625000000000000000000 : ℚ)⟩, [
    (118, modeDataJ4M119),
    (119, modeDataJ4M120),
    (120, modeDataJ4M121),
    (121, modeDataJ4M122),
    (122, modeDataJ4M123),
    (123, modeDataJ4M124)], (120521306759258098331/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b75 : entryChecks 4 bflatBlockJ4B75.entries = true := by
  simp only [entryChecks,bflatBlockJ4B75,List.all_cons,List.all_nil,
    mode_checked_j4_m119,
    mode_checked_j4_m120,
    mode_checked_j4_m121,
    mode_checked_j4_m122,
    mode_checked_j4_m123,
    mode_checked_j4_m124,Bool.and_self]
theorem block_mass_checked_j4_b75 : blockMassCheck bflatBlockJ4B75 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
