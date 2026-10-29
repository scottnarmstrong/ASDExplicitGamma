module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part004
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B66 : ModeBlockData :=
  ⟨⟨79, 88, (219658697036046187991/10000000000000000000000 : ℚ), (348312336777828147/10000000000000000000000 : ℚ)⟩, [
    (79, modeDataJ5M80),
    (80, modeDataJ5M81),
    (81, modeDataJ5M82),
    (82, modeDataJ5M83),
    (83, modeDataJ5M84),
    (84, modeDataJ5M85),
    (85, modeDataJ5M86),
    (86, modeDataJ5M87),
    (87, modeDataJ5M88)], (109829348518023093991/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b66 : entryChecks 5 bflatBlockJ5B66.entries = true := by
  simp only [entryChecks,bflatBlockJ5B66,List.all_cons,List.all_nil,
    mode_checked_j5_m80,
    mode_checked_j5_m81,
    mode_checked_j5_m82,
    mode_checked_j5_m83,
    mode_checked_j5_m84,
    mode_checked_j5_m85,
    mode_checked_j5_m86,
    mode_checked_j5_m87,
    mode_checked_j5_m88,Bool.and_self]
theorem block_mass_checked_j5_b66 : blockMassCheck bflatBlockJ5B66 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
