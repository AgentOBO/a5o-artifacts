/-
  Giza.lean — the A⁵O Clock Standard against the Great Pyramid (exploratory).

  Everything here is arithmetic on stated constants. The pyramid figures are
  the standard survey values (Petrie 1883; Lehner) rounded to whole units:
    royal cubit        = 7 palms = 28 fingers      (≈ 523.6 mm)
    Great Pyramid      base 440 cubits, height 280 cubits, perimeter 1760
    "Giza pi"          perimeter / height = 1760 / 280 = 44/7 = 2 · 22/7
  Clock constants are the sealed ones: period 17 500 ps, frequency 400/7 MHz.
  Core Lean 4 only; every theorem zero axioms.  Reading of the results is
  overlay and is labelled as such in the comments.
-/

namespace A5O.Giza

/-! ## Constants -/

def periodPs    : Nat := 17500          -- one tick, picoseconds
def freqNum     : Nat := 400 * 10 ^ 6   -- 400/7 MHz as a fraction
def freqDen     : Nat := 7
def secondPs    : Nat := 10 ^ 12

def palmsPerCubit    : Nat := 7
def fingersPerCubit  : Nat := 28
def baseCubits       : Nat := 440
def heightCubits     : Nat := 280
def perimeterCubits  : Nat := 4 * baseCubits

/-! ## 1. Seven is the cubit's divisor and the clock's denominator. -/

theorem cubit_denominator : palmsPerCubit = freqDen := rfl

theorem fingers_are_four_palms : fingersPerCubit = 4 * palmsPerCubit := rfl

/-! ## 2. The pyramid's height and base are multiples of the same 40. -/

theorem height_is_forty_sevens : heightCubits = 40 * 7 := rfl
theorem base_is_forty_elevens  : baseCubits   = 40 * 11 := rfl

/-- Overlay (a): the clock numerator is that same 40, times ten. -/
theorem clock_numerator_is_forty_tens : 400 = 40 * 10 := rfl

/-! ## 3. Giza pi.  perimeter / height = 44/7 = 2 · (22/7). -/

theorem giza_pi : perimeterCubits * 7 = 44 * heightCubits := by decide

/-- 22/7 and 400/7 have the SAME fractional part: 400 = 7·54 + 22, so
    400/7 = 54 + 22/7.  The clock frequency in MHz is Giza-pi plus 54.
    (Both numerators are ≡ 1 mod 7, hence both tails are 0.142857…) -/
theorem clock_is_giza_pi_plus_54 : 400 = 7 * 54 + 22 := by decide

theorem both_residue_one : 400 % 7 = 1 ∧ 22 % 7 = 1 := by decide

/-! ## 4. The period is seven remainders.  17 500 = 7 · 2 500. -/

theorem period_is_seven_remainders : periodPs = 7 * (secondPs % periodPs) := by decide

/-- Consequently the remainder needs exactly seven seconds to add up to one
    tick — the "seventh second resolves" theorem in ClockStandard.lean,
    seen from the other side. -/
theorem seven_remainders_make_a_tick : 7 * (secondPs % periodPs) = periodPs := by decide

/-! ## 5. Light in one tick ≈ ten royal cubits  (the one physical relation).

    c = 299 792 458 m/s (exact by definition of the metre).
    c · T = 299 792 458 · 17.5 ns = 5.246 368… m.
    Ten royal cubits at 523.6 mm = 5.236 m.
    Stated as integer bounds in micrometres so the kernel can decide it:
    the deviation is under 0.2 %. -/

def cPerSec_um     : Nat := 299792458 * 10 ^ 6          -- micrometres per second
def lightPerTick_um : Nat := cPerSec_um * periodPs / secondPs  -- = 5 246 368 µm (floor)
def cubit_um       : Nat := 523600                       -- Petrie 20.62 in ≈ 523.7 mm; 523.6 used

theorem light_per_tick_value : lightPerTick_um = 5246368 := by decide

/-- 10 cubits < light-per-tick < 10.02 cubits. -/
theorem light_per_tick_is_ten_cubits :
    10 * cubit_um < lightPerTick_um ∧ 1000 * lightPerTick_um < 10020 * cubit_um := by
  decide

/-- Overlay (b): with light-per-tick taken as ten cubits, the pyramid's
    dimensions become tick counts:  height 28 ticks, base 44 ticks,
    perimeter 176 ticks — and 176/28 = 44/7 is Giza pi again. -/
theorem height_in_ticks    : heightCubits    = 28 * 10 := rfl
theorem base_in_ticks      : baseCubits      = 44 * 10 := rfl
theorem perimeter_in_ticks : perimeterCubits = 176 * 10 := rfl
theorem tick_ratio_is_giza_pi : 176 * 7 = 44 * 28 := by decide

/-- Overlay (c): 28 — the height in ticks — is the number of fingers in a cubit. -/
theorem height_ticks_eq_fingers : heightCubits / 10 = fingersPerCubit := by decide

/-! ══════════════════════════════════════════════════════════════════════════
  ## 6. Framing — adopted by the Chairman, 2026-09-19.
  Drafted by Apertures in-session; adopted on his instruction "proceed with
  to include your framing". Three statements. The arithmetic under each is
  proved; the reading is his by adoption.
  ══════════════════════════════════════════════════════════════════════════ -/

/-! ### F1. The Clock Standard is a base-seven unit system, as the cubit is.
    Both fix a fundamental unit and divide it by seven: the cubit into palms,
    the second's worth of frequency into 400/7.  Every shared property —
    the 142857 tail, "Giza-pi plus 54", "seven remainders make a tick" —
    follows from that single shared choice. -/

theorem F1_same_divisor : palmsPerCubit = 7 ∧ freqDen = 7 := ⟨rfl, rfl⟩

/-! ### F2. Two resolutions of the non-terminating seventh.
    In base ten a seventh never closes.  The cubit closes it in SPACE:
    28 fingers, so a seventh of a cubit is exactly four fingers.
    The clock closes it in TIME: the 2 500 ps residue recurs seven times
    and lands exactly on the seventh second — 400 000 000 ticks, nothing
    carried.  Same fraction, one resolved by subdividing the unit, the other
    by waiting for the unit to recur. -/

/-- A seventh of a cubit is a whole number of fingers (four). -/
theorem F2_space : fingersPerCubit % 7 = 0 ∧ fingersPerCubit / 7 = 4 := by decide

/-- A seventh's residue closes in exactly seven seconds. -/
theorem F2_time : (7 * secondPs) % periodPs = 0 ∧ (7 * secondPs) / periodPs = 400000000 := by
  decide

/-- And not before: seconds one through six carry the residue. -/
theorem F2_time_not_before : ∀ s, s < 7 → s ≠ 0 → (s * secondPs) % periodPs ≠ 0 := by decide

/-! ### F3. One tick of light is ten cubits.
    c · 17.5 ns = 5.246 m; ten royal cubits = 5.236 m; the difference is
    under 0.2 %, inside the cubit's own measurement spread.  Under this
    pairing the Great Pyramid is 28 ticks high — the finger count of the
    cubit — 44 ticks wide, 176 ticks around, and 176/28 is Giza-pi.
    Held as a bounded coincidence: real, checkable, evidence of nothing
    beyond itself. -/

theorem F3_bound : 10 * cubit_um < lightPerTick_um ∧ 1000 * lightPerTick_um < 10020 * cubit_um :=
  light_per_tick_is_ten_cubits

theorem F3_pyramid_in_ticks :
    heightCubits / 10 = 28 ∧ baseCubits / 10 = 44 ∧ perimeterCubits / 10 = 176 ∧ 176 * 7 = 44 * 28 := by
  decide

end A5O.Giza

#print axioms A5O.Giza.cubit_denominator
#print axioms A5O.Giza.giza_pi
#print axioms A5O.Giza.clock_is_giza_pi_plus_54
#print axioms A5O.Giza.period_is_seven_remainders
#print axioms A5O.Giza.light_per_tick_value
#print axioms A5O.Giza.light_per_tick_is_ten_cubits
#print axioms A5O.Giza.tick_ratio_is_giza_pi
#print axioms A5O.Giza.height_ticks_eq_fingers
#print axioms A5O.Giza.F1_same_divisor
#print axioms A5O.Giza.F2_space
#print axioms A5O.Giza.F2_time
#print axioms A5O.Giza.F2_time_not_before
#print axioms A5O.Giza.F3_bound
#print axioms A5O.Giza.F3_pyramid_in_ticks
