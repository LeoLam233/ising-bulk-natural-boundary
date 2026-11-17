import IsingBulk.AnisoF002.C03.RegularRationalFirst
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Density of actual odd-denominator regular resonances

Odd primes give reduced positive rational angles in every subinterval
of (0,pi).  Their cosines are dense at every interior spectral coordinate.
This is the arithmetic input for dense physical boundary obstructions.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter
open scoped Topology

theorem regular_odd_fraction_between {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    ∃ r p : ℕ, 0 < r ∧ 2 * r < p ∧ r.Coprime p ∧ Odd p ∧
      a < (r : ℝ) / p ∧ (r : ℝ) / p < b := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (b - a))
  obtain ⟨p, hpN, hprime⟩ := Nat.exists_infinite_primes (max 3 N)
  have hp3 : 3 ≤ p := (le_max_left _ _).trans hpN
  have hp : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hNp : (N : ℝ) ≤ p := by exact_mod_cast (le_max_right 3 N).trans hpN
  have hwidth : 1 < (b - a) * p := by
    have hh := (div_lt_iff₀ (sub_pos.mpr hab)).mp (hN.trans_le hNp)
    nlinarith
  let r : ℕ := ⌊a * p⌋₊ + 1
  have hr : 0 < r := by dsimp [r]; omega
  have hleft : a * p < (r : ℝ) := by
    simpa only [r, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a * p)
  have hright : (r : ℝ) < b * p := by
    have hfloor := Nat.floor_le (mul_pos ha hp).le
    dsimp [r]
    push_cast
    nlinarith
  have hrp : 2 * r < p := by
    have hhalf := mul_lt_mul_of_pos_right hb hp
    have hh : 2 * (r : ℝ) < p := by nlinarith
    exact_mod_cast hh
  have hcop : r.Coprime p := by
    apply Nat.Coprime.symm
    apply hprime.coprime_iff_not_dvd.mpr
    intro hdiv
    have hle := Nat.le_of_dvd hr hdiv
    omega
  exact ⟨r, p, hr, hrp, hcop, hprime.odd_iff.mpr hp3,
    (lt_div_iff₀ hp).mpr hleft, (div_lt_iff₀ hp).mpr hright⟩

def regularOddFractions : Set ℝ :=
  {x | ∃ r p : ℕ, 0 < r ∧ 2 * r < p ∧ r.Coprime p ∧ Odd p ∧ x = (r : ℝ) / p}

def regularRationalCosines : Set ℝ :=
  {b | ∃ r p : ℕ, 0 < r ∧ 2 * r < p ∧ r.Coprime p ∧ Odd p ∧
    b = Real.cos (regularRationalAngle r p)}

theorem regularOddFractions_closure {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    x ∈ closure regularOddFractions := by
  apply mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨a, b, hxa, habU⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hU.inter isOpen_Ioo).mem_nhds ⟨hxU, hx⟩)
  let l := (a + x) / 2
  let u := (x + b) / 2
  have hl : l ∈ Ioo a b := by dsimp [l]; constructor <;> linarith [hxa.1, hxa.2]
  have hu : u ∈ Ioo a b := by dsimp [u]; constructor <;> linarith [hxa.1, hxa.2]
  have hlu : l < u := by dsimp [l, u]; linarith [hxa.1, hxa.2]
  obtain ⟨r, p, hr, hrp, hcop, hp, hlr, hru⟩ :=
    regular_odd_fraction_between (habU hl).2.1 hlu (habU hu).2.2
  refine ⟨(r : ℝ) / p, (habU ?_).1, r, p, hr, hrp, hcop, hp, rfl⟩
  exact ⟨hl.1.trans hlr, hru.trans hu.2⟩

theorem regularRationalCosines_closure {b : ℝ} (hb : |b| < 1) :
    b ∈ closure regularRationalCosines := by
  let x : ℝ := Real.arccos b / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hx : x ∈ Ioo (0 : ℝ) (1 / 2) := by
    constructor
    · exact div_pos (Real.arccos_pos.mpr (abs_lt.mp hb).2) hpi
    · apply (div_lt_iff₀ hpi).mpr
      have hh := Real.arccos_lt_pi.mpr (abs_lt.mp hb).1
      nlinarith
  have hc : ContinuousAt (fun u : ℝ => Real.cos (2 * Real.pi * u)) x := by fun_prop
  have himage := mem_closure_image hc (regularOddFractions_closure hx)
  have he : Real.cos (2 * Real.pi * x) = b := by
    dsimp [x]
    rw [mul_div_cancel₀ _ hpi.ne']
    exact Real.cos_arccos (abs_lt.mp hb).1.le (abs_lt.mp hb).2.le
  rw [he] at himage
  apply closure_mono ?_ himage
  rintro y ⟨u, ⟨r, p, hr, hrp, hcop, hp, rfl⟩, rfl⟩
  refine ⟨r, p, hr, hrp, hcop, hp, ?_⟩
  change Real.cos (2 * Real.pi * ((r : ℝ) / p)) = Real.cos (regularRationalAngle r p)
  apply congrArg Real.cos
  unfold regularRationalAngle
  ring

end
end IsingBulk.AnisoF002.RegularTail.C03
