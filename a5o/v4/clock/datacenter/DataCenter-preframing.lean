/-
  DataCenter.lean — one tick as a distance and latency budget (exploratory).

  Question: what does GateReadsLedger (the gate reads the ledger every tick)
  REQUIRE physically?  A read is a round trip.  The ledger must be close
  enough that a signal can go there and back inside 17 500 ps.

  Constants (stated, integer, in picoseconds and micrometres):
    c in vacuum        299 792 458 m/s
    signal in fibre    ~ c / 1.468  (single-mode, n ≈ 1.468)  ≈ 204 000 km/s
    signal in copper   ~ 0.7 c (PCB trace / twinax)           ≈ 210 000 km/s
    core at 3 GHz      one cycle = 333 ps  →  52 cycles per tick
    typical latencies  L1 ≈ 1 ns, L2 ≈ 4 ns, L3 ≈ 12 ns, DRAM ≈ 80 ns,
                       NIC-to-NIC same rack ≈ 2 µs, cross-AZ ≈ 1 ms
  Latency figures are order-of-magnitude industry values, stated as
  constants; the theorems are arithmetic on them.  Core Lean 4, zero axioms.
-/

namespace A5O.DC

def periodPs : Nat := 17500

/-! ## 1. One-way and round-trip reach per tick, in micrometres. -/

def um_per_s_vacuum : Nat := 299792458 * 10 ^ 6
def um_per_s_fibre  : Nat := 204200000 * 10 ^ 6
def um_per_s_copper : Nat := 210000000 * 10 ^ 6

def reach_um (v : Nat) : Nat := v * periodPs / 10 ^ 12          -- one way, per tick
def roundtrip_um (v : Nat) : Nat := reach_um v / 2               -- there and back

theorem vacuum_one_way   : reach_um um_per_s_vacuum = 5246368 := by decide  -- 5.25 m
theorem fibre_one_way    : reach_um um_per_s_fibre  = 3573500 := by decide  -- 3.57 m
theorem copper_one_way   : reach_um um_per_s_copper = 3675000 := by decide  -- 3.68 m
theorem fibre_round_trip : roundtrip_um um_per_s_fibre = 1786750 := by decide -- 1.79 m

/-- The ledger a gate reads every tick over fibre must sit within 1.79 m of
    the gate: the same rack, at most.  Not the next row.  Not the network. -/
theorem ledger_must_be_within_two_metres :
    roundtrip_um um_per_s_fibre < 2 * 10 ^ 6 := by decide

/-! ## 2. Distances in ticks. A replica d metres away is stale by ≥ this many ticks. -/

def ticks_one_way (d_um v : Nat) : Nat := (d_um * 10 ^ 12 + v * periodPs - 1) / (v * periodPs)  -- ceiling

theorem next_rack_600mm    : ticks_one_way 600000     um_per_s_copper = 1 := by decide
theorem across_hall_100m   : ticks_one_way 100000000  um_per_s_fibre  = 28 := by decide
theorem cross_campus_2km   : ticks_one_way 2000000000 um_per_s_fibre  = 560 := by decide

/-- 1 ms cross-AZ latency, in ticks: fifty-seven thousand. -/
def ps_to_ticks_ceil (ps : Nat) : Nat := (ps + periodPs - 1) / periodPs
theorem cross_az_1ms : ps_to_ticks_ceil (10 ^ 9) = 57143 := by decide

/-! ## 3. The core: 52 cycles per tick at 3 GHz. -/

def cyclePs_3GHz : Nat := 333   -- 1/3 ns, floored
theorem cycles_per_tick_3GHz : periodPs / cyclePs_3GHz = 52 := by decide

/-! ## 4. Memory: where the ledger snapshot can live if it is read every tick. -/

def L1_ps   : Nat := 1000
def L2_ps   : Nat := 4000
def L3_ps   : Nat := 12000
def DRAM_ps : Nat := 80000
def sameRackNIC_ps : Nat := 2000000

theorem L1_fits  : L1_ps   < periodPs := by decide
theorem L2_fits  : L2_ps   < periodPs := by decide
theorem L3_fits  : L3_ps   < periodPs := by decide
theorem DRAM_does_not : periodPs < DRAM_ps := by decide
theorem DRAM_in_ticks : ps_to_ticks_ceil DRAM_ps = 5 := by decide
theorem NIC_in_ticks  : ps_to_ticks_ceil sameRackNIC_ps = 115 := by decide

/-- Physical content of GateReadsLedger at one tick: the revocation snapshot
    lives in on-die cache (L1–L3), not DRAM and not on a network hop.  A
    gate whose ledger is one DRAM access away is a stalePass 5; one NIC hop
    away, stalePass 115.  Those are the exposure windows ClockStandard.lean
    proves for a stale gate. -/
theorem staleness_hierarchy :
    ps_to_ticks_ceil L3_ps = 1 ∧ ps_to_ticks_ceil DRAM_ps = 5 ∧
    ps_to_ticks_ceil sameRackNIC_ps = 115 ∧ ps_to_ticks_ceil (10 ^ 9) = 57143 := by
  decide

end A5O.DC

#print axioms A5O.DC.vacuum_one_way
#print axioms A5O.DC.fibre_round_trip
#print axioms A5O.DC.ledger_must_be_within_two_metres
#print axioms A5O.DC.across_hall_100m
#print axioms A5O.DC.cross_az_1ms
#print axioms A5O.DC.cycles_per_tick_3GHz
#print axioms A5O.DC.DRAM_does_not
#print axioms A5O.DC.staleness_hierarchy
