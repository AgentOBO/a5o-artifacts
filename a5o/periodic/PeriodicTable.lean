/-!
# PeriodicTable.lean — "Where does A⁵O sit on the periodic table"

Lean 4 (core only, no imports, no Mathlib). Prepared 2026-09-21 by Apertures
for AgentOBO Inc. from the chat of the same date.

Three kinds of content, kept apart by label:

* DATA    — recorded physical/chemical/historical values, entered from
            recall. Lean does not prove these. Lean proves only what follows
            from them arithmetically or structurally.
* MODEL   — a small state machine written to carry a mechanism described in
            the chat (heme seat, four-electron gate, spin rule, scram).
            Theorems are consequences of the model as written.
* OVERLAY — the mapping of any of this onto A⁵O. No formal content. §15
            proves that the file determines no such mapping.

The notation reading itself (A := argon, O := oxygen) is a named hypothesis
of record, not a theorem: §1.
-/

namespace A5O.Periodic

/-! ## §0  Types. Atomic number and mass number are different types. -/

structure AtomicNumber where
  val : Nat
  deriving DecidableEq, Repr

structure MassNumber where
  val : Nat
  deriving DecidableEq, Repr

structure Element where
  Z      : AtomicNumber
  group  : Nat          -- 0 = no group assignment (f-block)
  period : Nat
  deriving DecidableEq, Repr

-- DATA: positions on the table.
def He : Element := ⟨⟨2⟩, 18, 1⟩
def B  : Element := ⟨⟨5⟩, 13, 2⟩
def C  : Element := ⟨⟨6⟩, 14, 2⟩
def O  : Element := ⟨⟨8⟩, 16, 2⟩
def Al : Element := ⟨⟨13⟩, 13, 3⟩
def Ar : Element := ⟨⟨18⟩, 18, 3⟩
def K  : Element := ⟨⟨19⟩, 1, 4⟩
def Ca : Element := ⟨⟨20⟩, 2, 4⟩
def Fe : Element := ⟨⟨26⟩, 8, 4⟩
def Co : Element := ⟨⟨27⟩, 9, 4⟩
def Ni : Element := ⟨⟨28⟩, 10, 4⟩
def As : Element := ⟨⟨33⟩, 15, 4⟩
def Ag : Element := ⟨⟨47⟩, 11, 5⟩
def Te : Element := ⟨⟨52⟩, 16, 5⟩
def I  : Element := ⟨⟨53⟩, 17, 5⟩
def Au : Element := ⟨⟨79⟩, 11, 6⟩
def At : Element := ⟨⟨85⟩, 17, 6⟩
def Ac : Element := ⟨⟨89⟩, 3, 7⟩
def Am : Element := ⟨⟨95⟩, 0, 7⟩
def Cf : Element := ⟨⟨98⟩, 0, 7⟩
def Og : Element := ⟨⟨118⟩, 18, 7⟩

/-! ## §1  The reading, and what it depends on.

DATA: "A" was argon's official symbol until 1957; no other element has ever
carried the bare symbol "A". The reading A := Ar is that fact applied. -/

def sumReading (a o : Element) : Nat := a.Z.val + o.Z.val
def formulaReading (n : Nat) (a o : Element) : Nat := n * a.Z.val + o.Z.val

theorem sum_is_iron : sumReading Ar O = Fe.Z.val := by decide
theorem formula_is_californium : formulaReading 5 Ar O = Cf.Z.val := by decide
theorem exponent_is_boron : (5 : Nat) = B.Z.val := by decide

/-- Every current element whose symbol begins with "A". -/
def aInitial : List Element := [Al, Ar, As, Ag, Au, At, Ac, Am]

/-- The iron result holds under the argon reading and under no other
    A-initial reading. -/
theorem iron_only_under_argon :
    ∀ e ∈ aInitial, sumReading e O = Fe.Z.val → e = Ar := by decide

theorem group_gap : Ar.group = 18 ∧ O.group = 16 ∧ Ar.group - O.group = 2 := by decide

/-! ## §2  Exclusion: the rule beneath the table.

An electron address is (n, ℓ, mℓ, ms) with ℓ < n, mℓ ∈ [−ℓ, ℓ], ms ∈ {↑,↓}. -/

def orbitals (l : Nat) : Nat := 2 * l + 1
def subshellCap (l : Nat) : Nat := 2 * orbitals l

/-- Addresses in shell n: sum over ℓ < n of 2(2ℓ+1). -/
def shellCap : Nat → Nat
  | 0     => 0
  | n + 1 => shellCap n + subshellCap n

theorem five_d_orbitals : orbitals 2 = 5 := by decide

/-- General: shell n holds exactly 2n² addresses. -/
theorem shellCap_eq (n : Nat) : shellCap n = 2 * (n * n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show shellCap k + 2 * (2 * k + 1) = 2 * ((k + 1) * (k + 1))
    have e : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (k + 1) k, Nat.mul_add,
          Nat.mul_one, Nat.two_mul, Nat.add_assoc, Nat.add_assoc]
    rw [ih, e, Nat.mul_add 2 (k * k)]

/-- Helium is full: shell 1 has two addresses; any three electrons placed in
    it must repeat an address. -/
theorem shell_one_has_two : shellCap 1 = 2 := by decide
theorem no_third_electron : ∀ a b c : Fin 2, a = b ∨ b = c ∨ a = c := by decide

-- DATA: period lengths of the table.
def periodLengths : List Nat := [2, 8, 8, 18, 18, 32, 32]

theorem periods_are_shell_capacities :
    periodLengths = [shellCap 1, shellCap 2, shellCap 2, shellCap 3, shellCap 3,
                     shellCap 4, shellCap 4] := by decide

def cumulative : List Nat → List Nat
  | []      => []
  | x :: xs => x :: (cumulative xs).map (· + x)

/-- Running totals of the period lengths are the noble-gas atomic numbers. -/
theorem noble_gas_numbers :
    cumulative periodLengths = [2, 10, 18, 36, 54, 86, 118] := by decide

def nth : List Nat → Nat → Nat
  | [],      _     => 0
  | x :: _,  0     => x
  | _ :: xs, i + 1 => nth xs i

theorem argon_closes_period_three : nth (cumulative periodLengths) 2 = Ar.Z.val := by decide
theorem oganesson_closes_the_table :
    nth (cumulative periodLengths) 6 = Og.Z.val ∧ Og.group = Ar.group := by decide

/-- DATA: iron's ground configuration is [Ar] 3d⁶ 4s². So iron is an argon
    core plus eight electrons; 18 + 8 = 26 is a configuration fact, and the
    six d-electrons fit the ten d-addresses. That the eight equals oxygen's Z
    is a numeric coincidence. -/
theorem iron_is_argon_core_plus_eight :
    Ar.Z.val + (6 + 2) = Fe.Z.val ∧ 6 + 2 = O.Z.val ∧ 6 ≤ subshellCap 2 := by decide

/-! ## §3  Moseley: ordering by weight vs ordering by Z. -/

structure Weighed where
  el  : Element
  mDa : Nat            -- DATA: standard atomic weight, milli-daltons
  deriving DecidableEq

def ArW : Weighed := ⟨Ar, 39948⟩
def KW  : Weighed := ⟨K, 39098⟩
def CoW : Weighed := ⟨Co, 58933⟩
def NiW : Weighed := ⟨Ni, 58693⟩
def TeW : Weighed := ⟨Te, 127600⟩
def IW  : Weighed := ⟨I, 126904⟩

/-- Lower Z but heavier: weight order and Z order disagree. -/
abbrev Inversion (a b : Weighed) : Prop := a.el.Z.val < b.el.Z.val ∧ b.mDa < a.mDa

theorem three_inversions : Inversion ArW KW ∧ Inversion CoW NiW ∧ Inversion TeW IW := by decide

/-- Slots 18 and 19: slot 18 is the noble column, slot 19 the alkali column. -/
def groupAtSlot (s : Nat) : Nat := if s = 18 then 18 else if s = 19 then 1 else 0
def weightSlot (w rival : Weighed) : Nat := if w.mDa < rival.mDa then 18 else 19

/-- Ordered by weight, argon lands in the alkali column and potassium in the
    noble column. Ordered by Z, both land where their behaviour puts them. -/
theorem weight_order_misplaces :
    groupAtSlot (weightSlot ArW KW) = K.group ∧ groupAtSlot (weightSlot KW ArW) = Ar.group := by decide
theorem Z_order_places :
    groupAtSlot Ar.Z.val = Ar.group ∧ groupAtSlot K.Z.val = K.group := by decide

/-! ## §4  Argon. -/

-- DATA: dry air, parts per million by volume.
def ppmN2 : Nat := 780840
def ppmO2 : Nat := 209460
def ppmAr : Nat := 9340
def ppmCO2 : Nat := 420

theorem argon_third_in_air : ppmCO2 < ppmAr ∧ ppmAr < ppmO2 ∧ ppmO2 < ppmN2 := by decide
theorem argon_is_0_93_percent : ppmAr / 100 = 93 := by decide      -- 0.93 % in hundredths of a percent
theorem air_is_about_one_fifth_oxidizer : 5 * ppmO2 / 10000 = 104 := by decide  -- 5 × 20.9 % ≈ 104 %

-- DATA: Rayleigh's densities, g/L × 10⁴. Atmospheric "nitrogen" vs chemical nitrogen.
def rhoAtmos : Nat := 12572
def rhoChem  : Nat := 12505

/-- The residue was between 0.5 % and 0.6 % of the chemical value. -/
theorem rayleigh_residue :
    5 * rhoChem ≤ 1000 * (rhoAtmos - rhoChem) ∧ 1000 * (rhoAtmos - rhoChem) < 6 * rhoChem := by decide

-- DATA: isolation years. He is the terrestrial isolation.
def yearAr : Nat := 1894
def nobleYears : List Nat := [1895, 1898, 1898, 1898]   -- He, Ne, Kr, Xe

theorem column_filled_in_four_years : ∀ y ∈ nobleYears, y ≤ yearAr + 4 := by decide

/-- K-40 decays to Ar-40 (electron capture, Z − 1) and to Ca-40 (β⁻, Z + 1). -/
theorem potassium_argon_clock : K.Z.val - 1 = Ar.Z.val ∧ K.Z.val + 1 = Ca.Z.val := by decide

/-! ## §5  Oxygen-16 is doubly magic. -/

def magic : List Nat := [2, 8, 20, 28, 50, 82, 126]   -- DATA

structure Nuclide where
  Z : AtomicNumber
  N : Nat
  deriving DecidableEq

def Nuclide.A (x : Nuclide) : MassNumber := ⟨x.Z.val + x.N⟩

def O16 : Nuclide := ⟨O.Z, 8⟩

theorem oxygen_doubly_magic :
    magic.elem O16.Z.val = true ∧ magic.elem O16.N = true ∧ O16.A = ⟨16⟩ := by decide

/-! ## §6  The mass gaps, the triple-alpha bridge, the alpha ladder. -/

/-- DATA: no stable nuclide exists at mass number 5 or 8. -/
def noStableNuclide (a : MassNumber) : Bool := a.val == 5 || a.val == 8

def He4 : MassNumber := ⟨4⟩

theorem nucleon_step_lands_in_gap : noStableNuclide ⟨He4.val + 1⟩ = true := by decide
theorem alpha_step_lands_in_gap   : noStableNuclide ⟨He4.val + He4.val⟩ = true := by decide
theorem triple_alpha_clears_both  : noStableNuclide ⟨3 * He4.val⟩ = false ∧ 3 * He4.val = 12 := by decide
theorem then_oxygen               : 3 * He4.val + He4.val = O16.A.val := by decide

/-- The 5-and-8 echo. Oxygen's 8 is an `AtomicNumber`; the gap's 8 is a
    `MassNumber`. The numerals agree; the quantities cannot be equated — the
    statement `O.Z = gap8` does not typecheck (see NegativeControls.lean). -/
def gap5 : MassNumber := ⟨5⟩
def gap8 : MassNumber := ⟨8⟩
theorem echo_is_numeral_only : gap5.val = 5 ∧ O.Z.val = gap8.val := by decide

-- DATA: carbon-12 energies, keV.
def hoyleLevel  : Nat := 7654
def threeAlphaThreshold : Nat := 7275
theorem hoyle_state : hoyleLevel / 10 = 765 ∧ hoyleLevel - threeAlphaThreshold = 379 := by decide

/-- Alpha ladder: rung k is Z = 2k, A = 4k. -/
def rung (k : Nat) : Nuclide := ⟨⟨2 * k⟩, 2 * k⟩

theorem ladder_positions :
    rung 4 = O16 ∧ (rung 9).Z = Ar.Z ∧ (rung 9).A = ⟨36⟩ ∧
    (rung 14).Z = Ni.Z ∧ (rung 14).A = ⟨56⟩ := by decide

/-- Ni-56 → Co-56 → Fe-56: two β⁺ steps from the last rung reach iron. -/
theorem ladder_ends_in_iron : (rung 14).Z.val - 1 = Co.Z.val ∧ (rung 14).Z.val - 2 = Fe.Z.val := by decide

/-! ## §7  The iron peak, stated precisely. -/

-- DATA: binding energy per nucleon, units of 0.1 keV.
def bePerNucleon_Ni62 : Nat := 87945
def bePerNucleon_Fe58 : Nat := 87922
def bePerNucleon_Fe56 : Nat := 87903

theorem nickel62_tops_binding :
    bePerNucleon_Fe56 < bePerNucleon_Fe58 ∧ bePerNucleon_Fe58 < bePerNucleon_Ni62 := by decide

-- DATA: atomic masses, units of 10⁻⁷ u.
def mass_Fe56 : Nat := 559349363
def mass_Ni62 : Nat := 619283449

/-- Fe-56 has the lower mass per nucleon: m(Fe56)/56 < m(Ni62)/62. -/
theorem iron56_lowest_mass_per_nucleon : mass_Fe56 * 62 < mass_Ni62 * 56 := by decide

/-! ## §8  Degeneracy pressure: the address rule under load.

DATA: Chandrasekhar limit 1.4 M☉ (tenths). The neutron-level limit is left as
a parameter `tov`; only `14 < tov` is used. -/

def electronSupported (m : Nat) : Prop := m ≤ 14
def neutronSupported (tov m : Nat) : Prop := m ≤ tov

/-- A core above the electron limit and within the neutron limit fails at one
    level and is held at the next. -/
theorem collapse_then_caught (tov m : Nat) (h₁ : 14 < m) (h₂ : m ≤ tov) :
    ¬ electronSupported m ∧ neutronSupported tov m :=
  ⟨Nat.not_le.mpr h₁, h₂⟩

/-! ## §9  MODEL — the spin rule on oxygen.

Spins in units of 2S. Two spins a, b couple to totals |a−b|, |a−b|+2, …, a+b.
A reaction path exists iff reactants and products share a reachable total. -/

def couples (a b t : Nat) : Bool :=
  decide (max a b - min a b ≤ t) && decide (t ≤ a + b) && ((a + b - t) % 2 == 0)

def tripletO2 : Nat := 2
def singlet   : Nat := 0

/-- Path through mediator of spin c: reactants (O₂, mediator) and products
    (singlet products, mediator) share total t. -/
def pathExists (c t : Nat) : Bool := couples tripletO2 c t && couples singlet c t

/-- Deny by default: triplet O₂ with singlet fuel, all-singlet products, no mediator. -/
theorem direct_reaction_forbidden : ∀ t : Fin 8, pathExists 0 t.val = false := by decide

/-- High-spin Fe(II), S = 2 (2S = 4), opens a path. -/
theorem iron_opens_a_path : pathExists 4 4 = true := by decide

def anyPath (c : Nat) : Bool := (List.range 16).any (pathExists c)

/-- Within the modelled range (2S ≤ 7): a path exists iff the mediator has unpaired spin. -/
theorem path_iff_unpaired : ∀ c : Fin 8, anyPath c.val = decide (1 ≤ c.val) := by decide

/-! ## §10  MODEL — heme: five bonds on iron, the sixth seat for oxygen. -/

inductive Held | porphyrinN | proximalHis
  deriving DecidableEq

-- DATA: deoxy-heme iron is five-coordinate; octahedral iron has six positions.
def fixedLigands : List Held := [.porphyrinN, .porphyrinN, .porphyrinN, .porphyrinN, .proximalHis]
def octahedral : Nat := 6

theorem five_bonds : fixedLigands.length = 5 := by decide
theorem one_open_seat : octahedral - fixedLigands.length = 1 := by decide
theorem four_plus_one :
    fixedLigands.count .porphyrinN = 4 ∧ fixedLigands.count .proximalHis = 1 := by decide

inductive Ox | fe2 | fe3
  deriving DecidableEq
inductive Gas | O2 | CO
  deriving DecidableEq

structure Heme where
  pocket : Bool            -- the globin structure around the iron
  ox     : Ox
  sixth  : Option Gas
  deriving DecidableEq

/-- Binding. Only Fe(II) with an empty seat binds. Inside the pocket the gas is
    seated. Bare heme meeting O₂ is oxidised to Fe(III) and the seat stays empty. -/
def bind (g : Gas) (h : Heme) : Heme :=
  if h.ox = .fe2 ∧ h.sixth = none then
    if h.pocket then { h with sixth := some g }
    else if g = .O2 then { h with ox := .fe3 }
    else { h with sixth := some g }
  else h

def release (h : Heme) : Heme := { h with sixth := none }

def deoxyHb  : Heme := ⟨true, .fe2, none⟩
def bareHeme : Heme := ⟨false, .fe2, none⟩

/-- One seat: whatever holds it, a second gas is refused. -/
theorem seat_is_exclusive (g g' : Gas) (h : Heme) (hs : (bind g h).sixth ≠ none) :
    bind g' (bind g h) = bind g h := by
  generalize bind g h = s at hs
  cases s with
  | mk p o x =>
    cases x with
    | none => exact absurd rfl hs
    | some y => cases o <;> cases p <;> cases y <;> cases g' <;> rfl

/-- Revocable inside the structure. -/
theorem reversible_in_pocket : release (bind .O2 deoxyHb) = deoxyHb := by decide

/-- The same iron without the structure executes once and never carries again. -/
theorem bare_heme_is_ruined :
    (bind .O2 bareHeme).ox = .fe3 ∧ ∀ g, (bind g (bind .O2 bareHeme)).sixth = none := by
  refine ⟨by decide, ?_⟩
  intro g; cases g <;> decide

/-- The impostor takes the same seat, and then oxygen is refused. -/
theorem impostor_blocks_oxygen : bind .O2 (bind .CO deoxyHb) = bind .CO deoxyHb := by decide

-- DATA (MED confidence): CO : O₂ affinity ratio, bare heme vs inside the pocket.
def coRatioBare   : Nat := 20000
def coRatioPocket : Nat := 200

/-- The pocket's discrimination is a factor of 100: two orders of magnitude.
    The chat said "three orders of magnitude". That was wrong on its own
    figures; this theorem is the correction. -/
theorem pocket_discrimination :
    coRatioBare / coRatioPocket = 10 ^ 2 ∧ coRatioBare / coRatioPocket ≠ 10 ^ 3 := by decide

-- DATA: hemoglobin has four subunits; binding at one is communicated to the others.
theorem reporting_reaches_three : 4 - 1 = 3 := by decide

/-! ## §11  MODEL — cytochrome c oxidase: release only on the fourth electron. -/

inductive Outcome | held | water | reactiveOxygen
  deriving DecidableEq

def outcome (gated : Bool) (e : Fin 5) : Outcome :=
  if e.val = 4 then .water
  else if e.val = 0 then .held
  else if gated then .held else .reactiveOxygen

theorem gated_never_leaks : ∀ e : Fin 5, outcome true e ≠ .reactiveOxygen := by decide
theorem ungated_partial_leaks :
    ∀ e : Fin 5, 0 < e.val → e.val < 4 → outcome false e = .reactiveOxygen := by decide
theorem same_end_state : ∀ g : Bool, outcome g ⟨4, by decide⟩ = .water := by decide

/-- O₂ + 4e⁻ + 4H⁺ → 2H₂O balances in oxygen, hydrogen and charge. -/
theorem four_electron_balance : 2 = 2 * 1 ∧ 4 = 2 * 2 ∧ (4 : Int) - 4 = 0 := by decide

/-! ## §12  The banded-iron sink. Atmosphere = released − sink capacity (truncated). -/

theorem sink_holds : ∀ (released cap : Nat), released ≤ cap → released - cap = 0 := by
  intro r
  induction r with
  | zero => intro c _; exact Nat.zero_sub c
  | succ r ih =>
    intro c h
    cases c with
    | zero => exact absurd h (Nat.not_succ_le_zero r)
    | succ c => rw [Nat.succ_sub_succ]; exact ih c (Nat.le_of_succ_le_succ h)

theorem sink_filled : ∀ (released cap : Nat), cap < released → 0 < released - cap := by
  intro r
  induction r with
  | zero => intro c h; exact absurd h (Nat.not_lt_zero c)
  | succ r ih =>
    intro c h
    cases c with
    | zero => exact Nat.zero_lt_succ r
    | succ c => rw [Nat.succ_sub_succ]; exact ih c (Nat.lt_of_succ_lt_succ h)

/-! ## §13  MODEL — reactor: element 98 starts the chain, element 5 stops it.

Each generation: (carried + source) neutrons, each multiplied by k. Full
insertion of absorber sets k = 0 — the neutron is taken before the fission. -/

def nextGen (scram : Bool) (k source carried : Nat) : Nat :=
  (carried + source) * (if scram then 0 else k)

/-- Fail-closed: under scram the next generation is empty for every source
    strength, every multiplication factor, every prior population. -/
theorem scram_is_fail_closed (k s n : Nat) : nextGen true k s n = 0 := rfl

/-- The source alone starts the chain from nothing. -/
theorem source_initiates (k s : Nat) (hk : 0 < k) (hs : 0 < s) : 0 < nextGen false k s 0 := by
  show 0 < (0 + s) * k
  rw [Nat.zero_add]; exact Nat.mul_pos hs hk

theorem initiator_and_terminator :
    formulaReading B.Z.val Ar O = Cf.Z.val := by decide

/-! ## §14  The edge of the table. -/

-- DATA: 1/α ≈ 137.036. In the point-nucleus model the 1s electron has v/c = Zα.
def alphaInvMilli : Nat := 137036

/-- Zα < 1 exactly when Z ≤ 137. -/
theorem point_nucleus_limit (Z : Nat) : Z * 1000 < alphaInvMilli ↔ Z ≤ 137 := by
  constructor
  · intro h
    cases Nat.lt_or_ge 137 Z with
    | inl hgt =>
      have h₁ : 138 * 1000 ≤ Z * 1000 := Nat.mul_le_mul_right 1000 hgt
      have h₂ : 138 * 1000 < alphaInvMilli := Nat.lt_of_le_of_lt h₁ h
      exact absurd h₂ (by decide)
    | inr hle => exact hle
  · intro h
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 1000 h) (by decide)

-- DATA (MED confidence): finite-nucleus breakdown near Z = 173.
theorem known_table_inside_both_limits : Og.Z.val < 137 ∧ 137 < 173 := by decide

/-! ## §15  OVERLAY boundary.

The five A⁵O conditions and the three fives found above (heme bonds,
d-orbitals, boron's Z) agree in count. The file proves that and proves that
count is all it supplies: more than one assignment of conditions to places
exists, and nothing above selects among them. -/

inductive Condition | appointment | agent | authority | accountability | auditability
  deriving DecidableEq

def conditions : List Condition :=
  [.appointment, .agent, .authority, .accountability, .auditability]

theorem fives_agree_in_count :
    conditions.length = fixedLigands.length ∧ conditions.length = orbitals 2 ∧
    conditions.length = B.Z.val := by decide

def asListed : Condition → Nat
  | .appointment => 0 | .agent => 1 | .authority => 2 | .accountability => 3 | .auditability => 4

def swapped : Condition → Nat
  | .appointment => 4 | .agent => 1 | .authority => 2 | .accountability => 3 | .auditability => 0

theorem both_land_in_five_places : ∀ c ∈ conditions, asListed c < 5 ∧ swapped c < 5 := by decide

def Injective {α β : Type} (f : α → β) : Prop := ∀ a b, f a = f b → a = b

theorem asListed_injective : Injective asListed := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem swapped_injective : Injective swapped := by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The notation alone forces no mapping. -/
theorem notation_forces_no_mapping :
    ∃ f g : Condition → Nat, Injective f ∧ Injective g ∧ f ≠ g :=
  ⟨asListed, swapped, asListed_injective, swapped_injective,
   fun h => absurd (congrFun h .appointment) (by decide)⟩

end A5O.Periodic
