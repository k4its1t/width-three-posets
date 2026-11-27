import Std

/-! Exact finite calculation used in the 14-state bound for 7-thin posets of
width at most three. A natural number represents the membership mask of an ideal. -/

namespace ThinWidthRank

private def pattern (u v state : Nat) : Bool := state.testBit u && !state.testBit v

private def avoid (u v : Nat) (pool : List Nat) : List Nat :=
  pool.filter fun state => !pattern u v state

/-- The neighbors that are forced to be incomparable by two opposing states. -/
def neighbors (m : Nat) (family : List Nat) (u : Nat) : List Nat :=
  (List.range m).filter fun v => family.any (pattern u v) && family.any (pattern v u)

private def codeSlot (code i : Nat) : Nat := (code >>> (4*i)) % 16

private def validPivot (m u : Nat) (vs : List Nat) : Bool :=
  decide (u < m ∧ vs.Nodup ∧ vs.length = 8) && vs.all (· < m)

private def checkEach (check : List Nat → Nat → Option (List Nat)) :
    List Nat → List Nat → Option (List Nat)
  | [], steps => some steps
  | v :: vs, steps => (check steps v).bind (checkEach check vs)

private theorem checkEach_hit {check : List Nat → Nat → Option (List Nat)}
    {vs start rest : List Nat} {v : Nat}
    (hc : checkEach check vs start = some rest) (hv : v ∈ vs) :
    ∃ a b, check a v = some b := by
  induction vs generalizing start with
  | nil => simp at hv
  | cons u us ih =>
    simp only [checkEach] at hc
    cases h : check start u with
    | none => simp [h] at hc
    | some next =>
      rw [h] at hc
      rcases List.mem_cons.mp hv with hEq | hTail
      · exact ⟨start, next, hEq ▸ h⟩
      · exact ih hc hTail

private def refute (m : Nat) : Nat → List Nat → List Nat → Option (List Nat)
  | 0, pool, steps => if pool.length ≤ 14 then some steps else none
  | fuel + 1, pool, steps =>
    if pool.length ≤ 14 then some steps
    else match steps with
      | [] => none
      | code :: remaining =>
        let u := codeSlot code 0
        let vs := (List.range 8).map fun i => codeSlot code (i+1)
        if validPivot m u vs then
          checkEach (fun s v => (refute m fuel (avoid u v pool) s).bind
            (refute m fuel (avoid v u pool))) vs remaining
        else none

private theorem subset_avoid {family pool : List Nat} {u v : Nat} (hs : family ⊆ pool)
    (ha : family.any (pattern u v) = false) : family ⊆ avoid u v pool := by
  intro s hm
  apply List.mem_filter.mpr
  refine ⟨hs hm, ?_⟩
  cases h : pattern u v s with
  | false => rfl
  | true =>
    have ht : family.any (pattern u v) = true := List.any_eq_true.mpr ⟨s, hm, h⟩
    simp [ha] at ht

private theorem missing_direction {family : List Nat} {m u v : Nat}
    (hv : v < m) (hn : v ∉ neighbors m family u) :
    family.any (pattern u v) = false ∨ family.any (pattern v u) = false := by
  by_cases hp : family.any (pattern u v) = true
  · right
    cases hq : family.any (pattern v u) with
    | false => rfl
    | true => exact (hn (List.mem_filter.mpr ⟨List.mem_range.mpr hv, by simp [hp, hq]⟩)).elim
  · left
    cases h : family.any (pattern u v) with
    | false => rfl
    | true => exact (hp h).elim

private theorem refute_sound {m fuel : Nat} {pool family steps rest : List Nat}
    (hc : refute m fuel pool steps = some rest) (hs : family ⊆ pool) (hn : family.Nodup)
    (hd : ∀ u < m, (neighbors m family u).length ≤ 7) : family.length ≤ 14 := by
  induction fuel generalizing pool steps rest with
  | zero =>
    by_cases hp : pool.length ≤ 14
    · exact Nat.le_trans (hn.length_le_of_subset hs) hp
    · simp [refute, hp] at hc
  | succ fuel ih =>
    by_cases hp : pool.length ≤ 14
    · exact Nat.le_trans (hn.length_le_of_subset hs) hp
    simp only [refute, hp, ite_false] at hc
    cases steps with
    | nil => simp at hc
    | cons code remaining =>
      let u := codeSlot code 0
      let vs := (List.range 8).map fun i => codeSlot code (i+1)
      change (if validPivot m u vs then
        checkEach (fun s v => (refute m fuel (avoid u v pool) s).bind
          (refute m fuel (avoid v u pool))) vs remaining else none) = some rest at hc
      by_cases hvp : validPivot m u vs = true
      · simp only [hvp, ite_true] at hc
        have hv : (u < m ∧ vs.Nodup ∧ vs.length = 8) ∧ (∀ v ∈ vs, v < m) := by
          simpa [validPivot] using hvp
        have hm : ∃ v ∈ vs, v ∉ neighbors m family u := by
          apply Classical.byContradiction
          intro h
          have hsub : vs ⊆ neighbors m family u := by
            intro v hmem
            exact Classical.byContradiction fun hm => h ⟨v, hmem, hm⟩
          have hle := hv.1.2.1.length_le_of_subset hsub
          have hd' := hd u hv.1.1
          omega
        obtain ⟨v, hmem, hnot⟩ := hm
        obtain ⟨initial, final, hBoth⟩ := checkEach_hit hc hmem
        cases hFirst : refute m fuel (avoid u v pool) initial with
        | none => simp [hFirst] at hBoth
        | some middle =>
          rw [hFirst] at hBoth
          rcases missing_direction (hv.2 v hmem) hnot with ha | ha
          · exact ih hFirst (subset_avoid hs ha)
          · exact ih hBoth (subset_avoid hs ha)
      · simp [hvp] at hc

/-- The mask of three prefixes of lengths `x`, `y`, `z`, in three consecutive blocks. -/
def mask (a b x y z : Nat) : Nat :=
  (2^x - 1) + ((2^y - 1) <<< a) + ((2^z - 1) <<< (a + b))

/-- Masks for the unrestricted slice of three chain prefixes with total size `r`. -/
def slice (a b c r : Nat) : List Nat :=
  (List.range (a + 1)).flatMap fun x =>
    (List.range (b + 1)).filterMap fun y =>
      if x + y ≤ r && r - (x + y) ≤ c then some (mask a b x y (r - (x + y))) else none

theorem mask_mem_slice {a b c x y z r : Nat}
    (hx : x ≤ a) (hy : y ≤ b) (hz : z ≤ c) (hr : x + y + z = r) :
    mask a b x y z ∈ slice a b c r := by
  apply List.mem_flatMap.mpr
  refine ⟨x, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨y, List.mem_range.mpr (by omega), ?_⟩
  have hxy : x + y ≤ r := by omega
  have hz' : r - (x + y) = z := by omega
  simp [hxy, hz', hz]

/- Each word stores the pivot followed by eight distinct neighbors, in 4-bit slots. -/
private def hintsFor (a b c r : Nat) : List Nat :=
  match a, b, c, r with
  | 2, 4, 6, 6 => [0x987654320]
  | 2, 4, 7, 6 => [0x987654320]
  | 2, 5, 5, 5 => [0x987654320]
  | 2, 5, 5, 6 => [0xa98754320]
  | 2, 5, 6, 6 =>
    [0x752a98430, 0xa98765430, 0xba9874320, 0xa98654320]
  | 2, 5, 7, 7 =>
    [0x52b84a930, 0xcba987320, 0xba9654320, 0x987654320, 0xcba985430, 0xcba985431]
  | 2, 6, 6, 7 =>
    [0xd810cba94, 0xdcba98320, 0xba9865430, 0x962ba5430, 0xba9765430, 0xcba954320, 0xba7654320,
     0xb86a95430, 0xba9854320, 0xa97654320, 0x987654320]
  | 3, 3, 5, 5 => [0xa98765430]
  | 3, 3, 6, 5 => [0xa98765430]
  | 3, 3, 6, 6 => [0x6a9875431, 0xba9875430]
  | 3, 3, 7, 6 => [0x6a9875431, 0xba9875430]
  | 3, 4, 4, 5 => [0xa98765431]
  | 3, 4, 5, 5 =>
    [0x763a98541, 0xa98765430, 0xba9875430, 0xa98765430]
  | 3, 4, 5, 6 =>
    [0x763a98541, 0xba9876541, 0xba9875431, 0xba9865431]
  | 3, 4, 6, 6 =>
    [0x63b854a91, 0xa98765430, 0xcba987430, 0xba9865430, 0xa98765431, 0x764ba9851, 0xa98765430,
     0xba9875430, 0xba9865430, 0x753ba9841, 0xba9875430, 0xcba987430, 0xcba985430]
  | 3, 4, 7, 7 =>
    [0x3c854b9a1, 0xcba965430, 0xa98765430, 0x3cba98540, 0xba9876540, 0x7cba98431, 0xdcba98430,
     0x963cba541, 0xcba965430, 0xdcba95430, 0xcba965430, 0xb63a98541, 0xba9876540, 0xba9875430,
     0xa98765430, 0x64c8ba951, 0xcba965430, 0xba9876540, 0x3cba98540, 0xba9876540, 0x7cba98541,
     0xcba985430]
  | 3, 5, 5, 6 =>
    [0xc820ba915, 0xa98765430, 0x863ba9541, 0xba9876541, 0xcba985431, 0xba9765431, 0xb63a98540,
     0xba9876540, 0xcba985430, 0xa98765430, 0xc93ba6541, 0xba9765430, 0xba9765430, 0xba9765430,
     0x873a96541, 0xba9876541, 0xba9865431, 0xba9765431]
  | 3, 5, 6, 7 =>
    [0x73206145a, 0xcba987650, 0xdcb765431, 0x6dcba5431, 0xdcba95430, 0x73b6a9541, 0xcba985431,
     0xa98765431, 0xba9876541, 0xcba985431, 0xd290cba15, 0xcba965431, 0x7cba65430, 0xdcba65430,
     0xc63ba9540, 0xba9876540, 0xcba985430, 0xa98765430, 0x973ba6541, 0xba9876540, 0xba9865430,
     0xba9765430, 0x74c965ba1, 0xba9876540, 0xdcba98540, 0xcba976540, 0xba9876541, 0x875cba961,
     0xba9876540, 0xcba986540, 0xcba976540, 0x864cba951, 0xcba986540, 0xdcba98540, 0xdcba96540,
     0x639c54ba1, 0xba9865430, 0xdcba98430, 0xba9865430, 0xdcba65431, 0xd64cba951, 0xba9865430,
     0xcba985430, 0xcba986540, 0xd53cba941, 0xcba985430, 0xdcba98430, 0xcba985430]
  | 4, 4, 4, 5 =>
    [0xb784a9651, 0xba9876540, 0xba9876540, 0xba9832105, 0x765432109]
  | 4, 4, 4, 6 =>
    [0xb784a6951, 0xba9876542, 0xba9876542, 0xba9832106, 0x76543210a, 0xb30a98215, 0xba9876542,
     0xba9876542, 0xba9876542, 0x730654219, 0xba9876542, 0xba9876542, 0xba9876542]
  | 4, 4, 5, 6 =>
    [0x74306521a, 0xba9876542, 0xba9876540, 0xba9876540, 0xcba986540, 0x84b7a9652, 0xcba986541,
     0x765432108, 0x4ba987651, 0xcba987651, 0x8ba976541, 0xcba976541, 0x874ba9651, 0xcba987651,
     0xcba986541, 0xcba976541, 0x80b3a9216, 0xcba987650, 0x765432108, 0x4ba987652, 0xcba987651,
     0x8ba932105, 0xcba976540, 0x830ba9215, 0xcba986542, 0xcba986541, 0xcba932105]
  | 4, 4, 6, 7 =>
    [0x73406251a, 0xba9876542, 0xdcba76540, 0xcba987650, 0xdcba76540, 0xda7cb6541, 0xdcba96540,
     0xdcba76540, 0xcba976540, 0x7dcba6541, 0xcba976540, 0xdcba32105, 0x74c965ba2, 0xba9876541,
     0xdcba98541, 0xcba976541, 0xba9876542, 0x875cba962, 0xba9876541, 0xcba986541, 0xcba976541,
     0x864cba952, 0xcba986541, 0xdcba98541, 0xdcba96541, 0x87c56ba91, 0xcba987652, 0xcba982106,
     0xba9832106, 0x831cba926, 0xcba987652, 0xdcba98650, 0xdcba97652, 0xd7cba9651, 0xdcba97652,
     0xcba932106, 0x794c6a5b1, 0xba9876540, 0xdcba76540, 0xdcba96542, 0x8ba976541, 0xcba976542,
     0xd75cba961, 0xba9876540, 0xcba986540, 0xcba987650, 0xda7cb6541, 0xdcba32104, 0xdcba76540,
     0x76543210b, 0xd694cba51, 0xcba986540, 0xdcba32104, 0xdcba96542, 0x8cba96541, 0xcba976542,
     0x390c2a1b5, 0xcba986542, 0xdcba76540, 0xdcba92106, 0x8ba932105, 0xcba976540, 0xd64cba952,
     0xcba986541, 0xdcba98541, 0xcba986541, 0x7dcba6541, 0x76543210b, 0xdcba32105, 0xd496cba51,
     0xdcba98540, 0xdcba76540, 0xdcba92106, 0x7cba96541, 0xcba986540]
  | 4, 5, 5, 7 =>
    [0x93021cab6, 0xdcba76540, 0xcba987650, 0x40736521c, 0xdcb876540, 0xdcba32104, 0x8dcb76542,
     0xdcba76541, 0x47653210b, 0xdcba87650, 0x83507621a, 0xba9876541, 0xcba932107, 0x4ba987651,
     0xcba987650, 0x47653210a, 0xcba987650, 0x74d6cba52, 0xcba976543, 0xba9876542, 0xdcba97652,
     0xdcba93215, 0xcba987650, 0xcba976543, 0x8596cba71, 0xcba987650, 0xcba876540, 0xdcba92107,
     0xdcba97651, 0xd9312cab6, 0xdcba76541, 0xba9876541, 0xcba976543, 0xba9876541, 0x74d6cba52,
     0xcba976543, 0xba9876542, 0xdcba97652, 0xdcba93215, 0x74c96ba51, 0xba9876542, 0xcba876541,
     0xba9876541, 0xdcba97651, 0xdcba97652, 0xa4d7cb652, 0xdcba32104, 0xcba876541, 0x4dcba7651,
     0xdcba87651, 0x8dcb76541, 0xdcba76541, 0x984ba7652, 0xcba987652, 0xcba976542, 0xcba876542,
     0xd9201cab6, 0xdcb876540, 0xcba987650, 0xba9876542, 0xcba987650, 0x74c96ba51, 0xba9876542,
     0xcba876541, 0xba9876541, 0xdcba97651, 0xdcba97652, 0x8596cba71, 0xcba987650, 0xcba876540,
     0xdcba92107, 0xdcba97651, 0xa84cb7651, 0xdcba87651, 0xdcba76541, 0xdcb876541, 0xc895ba761,
     0xcba932107, 0xcba876540, 0x4cba97651, 0xcba987652, 0x4ba987651, 0xcba987652, 0xda30cb216,
     0xdcba76542, 0xcba876540, 0xdcba76540, 0xcba876540, 0xa4d7cb652, 0xdcba32104, 0xcba876541,
     0x4dcba7651, 0xdcba87651, 0x8dcb76541, 0xdcba76541, 0xa84cb7651, 0xdcba87651, 0xdcba76541,
     0xdcb876541, 0x40736521c, 0xdcb876540, 0xdcba32104, 0x8dcb76542, 0xdcba76541, 0x47653210b,
     0xdcba87650, 0x43076521b, 0xcba876542, 0xcba876541, 0x87653210b]
  | _, _, _, _ => []
-- 23 slices use certificates with a total of 371 split steps.

private def verifyWidth (c : Nat) : Bool :=
  (List.range (c + 1)).all fun a =>
    (List.range (c + 1)).all fun b =>
      (List.range 8).all fun r =>
        if a ≤ b ∧ 2*r ≤ a+b+c ∧ a+b+c ≤ r+7 then
          decide (refute (a+b+c) 10 (slice a b c r) (hintsFor a b c r) = some [])
        else true

-- Each calculation is closed and checked by kernel reduction.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem widthsVerified : (List.range 8).all verifyWidth = true := by
  decide +kernel

/-- Every distinct family of masks in one admissible slice that forces at most
seven incomparable neighbors per vertex has cardinality at most fourteen. -/
theorem fourteen {a b c r : Nat} {family : List Nat}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 7) (hr : r ≤ 7)
    (hdu : 2*r ≤ a+b+c) (hm : a+b+c ≤ r+7)
    (hsub : family ⊆ slice a b c r) (hn : family.Nodup)
    (hd : ∀ u < a+b+c, (neighbors (a+b+c) family u).length ≤ 7) : family.length ≤ 14 := by
  have hv := List.all_eq_true.mp (List.all_eq_true.mp widthsVerified c (List.mem_range.mpr (by omega)))
  have ha := List.all_eq_true.mp (hv a (List.mem_range.mpr (by omega)))
  have hb := List.all_eq_true.mp (ha b (List.mem_range.mpr (by omega)))
  have h := hb r (List.mem_range.mpr (by omega))
  have hshape : a ≤ b ∧ 2 * r ≤ a+b+c ∧ a+b+c ≤ r+7 := ⟨hab, hdu, hm⟩
  simp only [hshape] at h
  exact refute_sound (of_decide_eq_true h) hsub hn hd

/-- The disjoint union of chains of lengths 3, 3, and 4 has fourteen
order ideals of size five, one for each member of its unrestricted slice. -/
theorem sharpSlice : (slice 3 3 4 5).length = 14 ∧ (slice 3 3 4 5).Nodup ∧
    ((List.range 10).all fun u => (neighbors 10 (slice 3 3 4 5) u).length ≤ 7) = true := by
  decide +kernel

/-! The following calculations verify the four rows of the prefix certificate. -/

private def predecessorMask (u : Nat) : Nat :=
  (#[0, 0, 1, 2, 3, 5, 31, 63, 127, 191, 511][u]?).getD 0

private def prefixOrders : Nat → List (List Nat × Nat)
  | 0 => [([], 0)]
  | k + 1 => (prefixOrders k).flatMap fun (word, used) =>
    (List.range 11).filterMap fun u =>
      let required := predecessorMask u
      if !used.testBit u && (used &&& required) == required then
        some (word ++ [u], used + 2^u)
      else none

private def prefixRow (ideal : Nat) : Nat × Nat × Nat :=
  let orders := (prefixOrders 4).filterMap fun (word, used) =>
    if used == ideal then some word else none
  (orders.length, (orders.filter fun word => word.idxOf 1 < word.idxOf 0).length,
    (orders.filter fun word => word.idxOf 2 < word.idxOf 1).length)

/-- The final mask and the counts of the two reversals in each legal prefix. -/
theorem prefixTable :
    ((prefixOrders 4).all fun (_, mask) => [15, 23, 27, 39].contains mask) = true ∧
    [15, 23, 27, 39].map prefixRow = [(6, 3, 1), (5, 2, 1), (5, 3, 0), (4, 1, 2)] := by
  decide +kernel

/-- For arbitrary completion multiplicities, at least one reversal is balanced. -/
theorem prefixWeighted (a b c d : Nat) :
    let total := 6*a + 5*b + 5*c + 4*d
    let p := 3*a + 2*b + 3*c + d
    let q := a + b + 2*d
    (total ≤ 3*p ∧ 3*p ≤ 2*total) ∨ (total ≤ 3*q ∧ 3*q ≤ 2*total) := by
  dsimp
  omega

#print axioms ThinWidthRank.fourteen
#print axioms ThinWidthRank.sharpSlice
#print axioms ThinWidthRank.prefixTable
#print axioms ThinWidthRank.prefixWeighted

end ThinWidthRank
