module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part007
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B70 : ModeBlockData :=
  ⟨⟨118, 130, (281570982652834251563/10000000000000000000000 : ℚ), (90604430067547593/2000000000000000000000 : ℚ)⟩, [
    (118, modeDataJ5M119),
    (119, modeDataJ5M120),
    (120, modeDataJ5M121),
    (121, modeDataJ5M122),
    (122, modeDataJ5M123),
    (123, modeDataJ5M124),
    (124, modeDataJ5M125),
    (125, modeDataJ5M126),
    (126, modeDataJ5M127),
    (127, modeDataJ5M128),
    (128, modeDataJ5M129),
    (129, modeDataJ5M130)], (281570982652834251551/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b70 : entryChecks 5 bflatBlockJ5B70.entries = true := by
  simp only [entryChecks,bflatBlockJ5B70,List.all_cons,List.all_nil,
    mode_checked_j5_m119,
    mode_checked_j5_m120,
    mode_checked_j5_m121,
    mode_checked_j5_m122,
    mode_checked_j5_m123,
    mode_checked_j5_m124,
    mode_checked_j5_m125,
    mode_checked_j5_m126,
    mode_checked_j5_m127,
    mode_checked_j5_m128,
    mode_checked_j5_m129,
    mode_checked_j5_m130,Bool.and_self]
theorem block_mass_checked_j5_b70 : blockMassCheck bflatBlockJ5B70 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
