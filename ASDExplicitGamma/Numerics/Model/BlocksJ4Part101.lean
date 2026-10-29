module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part028
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part029

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B101 : ModeBlockData :=
  ⟨⟨449, 472, (491219080854330823/5000000000000000000000 : ℚ), (464250077277779127/10000000000000000000000 : ℚ)⟩, [
    (449, modeDataJ4M450),
    (450, modeDataJ4M451),
    (451, modeDataJ4M452),
    (452, modeDataJ4M453),
    (453, modeDataJ4M454),
    (454, modeDataJ4M455),
    (455, modeDataJ4M456),
    (456, modeDataJ4M457),
    (457, modeDataJ4M458),
    (458, modeDataJ4M459),
    (459, modeDataJ4M460),
    (460, modeDataJ4M461),
    (461, modeDataJ4M462),
    (462, modeDataJ4M463),
    (463, modeDataJ4M464),
    (464, modeDataJ4M465),
    (465, modeDataJ4M466),
    (466, modeDataJ4M467),
    (467, modeDataJ4M468),
    (468, modeDataJ4M469),
    (469, modeDataJ4M470),
    (470, modeDataJ4M471),
    (471, modeDataJ4M472)], (982438161708661623/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b101 : entryChecks 4 bflatBlockJ4B101.entries = true := by
  simp only [entryChecks,bflatBlockJ4B101,List.all_cons,List.all_nil,
    mode_checked_j4_m450,
    mode_checked_j4_m451,
    mode_checked_j4_m452,
    mode_checked_j4_m453,
    mode_checked_j4_m454,
    mode_checked_j4_m455,
    mode_checked_j4_m456,
    mode_checked_j4_m457,
    mode_checked_j4_m458,
    mode_checked_j4_m459,
    mode_checked_j4_m460,
    mode_checked_j4_m461,
    mode_checked_j4_m462,
    mode_checked_j4_m463,
    mode_checked_j4_m464,
    mode_checked_j4_m465,
    mode_checked_j4_m466,
    mode_checked_j4_m467,
    mode_checked_j4_m468,
    mode_checked_j4_m469,
    mode_checked_j4_m470,
    mode_checked_j4_m471,
    mode_checked_j4_m472,Bool.and_self]
theorem block_mass_checked_j4_b101 : blockMassCheck bflatBlockJ4B101 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
