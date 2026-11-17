import IsingBulk.AnisoF002.C03.IsotropicPrimeGeometry
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Density of the actual isotropic prime family

Primes can be required to exceed any prescribed finite threshold.
In particular the six-term uniqueness proof's p >= 7 family is dense
in both open upper quadrants, and in every smaller open angular chart.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology

theorem isotropic_prime_fraction_between (K : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    ∃ r p : ℕ, K ≤ p ∧ p.Prime ∧ 0 < r ∧ 2 * r < p ∧ r.Coprime p ∧
      a < (r : ℝ) / p ∧ (r : ℝ) / p < b := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (b - a))
  obtain ⟨p, hpN, hprime⟩ := Nat.exists_infinite_primes (max K N)
  have hp : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  have hNp : (N : ℝ) ≤ p := by exact_mod_cast (le_max_right K N).trans hpN
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
  exact ⟨r, p, (le_max_left _ _).trans hpN, hprime, hr, hrp, hcop,
    (lt_div_iff₀ hp).mpr hleft, (div_lt_iff₀ hp).mpr hright⟩

def isotropicPrimeFractions : Set ℝ :=
  {x | ∃ r p : ℕ, 7 ≤ p ∧ p.Prime ∧ 0 < r ∧ 2 * r < p ∧ r.Coprime p ∧ x = (r : ℝ) / p}

def isotropicPrimeAngles : Set ℝ :=
  {α | ∃ r p : ℕ, 7 ≤ p ∧ p.Prime ∧ 0 < r ∧ 2 * r < p ∧ r.Coprime p ∧
    α = isotropicPrimeAngle p r}

theorem isotropicPrimeFractions_closure {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    x ∈ closure isotropicPrimeFractions := by
  apply mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨a, b, hxa, habU⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hU.inter isOpen_Ioo).mem_nhds ⟨hxU, hx⟩)
  let l := (a + x) / 2
  let u := (x + b) / 2
  have hl : l ∈ Ioo a b := by dsimp [l]; constructor <;> linarith [hxa.1, hxa.2]
  have hu : u ∈ Ioo a b := by dsimp [u]; constructor <;> linarith [hxa.1, hxa.2]
  have hlu : l < u := by dsimp [l, u]; linarith [hxa.1, hxa.2]
  obtain ⟨r, p, hp7, hp, hr, hrp, hcop, hlr, hru⟩ :=
    isotropic_prime_fraction_between 7 (habU hl).2.1 hlu (habU hu).2.2
  refine ⟨(r : ℝ) / p, (habU ?_).1, r, p, hp7, hp, hr, hrp, hcop, rfl⟩
  exact ⟨hl.1.trans hlr, hru.trans hu.2⟩

theorem isotropicPrimeAngles_closure {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) Real.pi) :
    α ∈ closure isotropicPrimeAngles := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let x : ℝ := α / (2 * Real.pi)
  have hx : x ∈ Ioo (0 : ℝ) (1 / 2) := by
    refine ⟨div_pos hα.1 hpi, ?_⟩
    apply (div_lt_iff₀ hpi).mpr
    nlinarith [hα.2]
  have hc : ContinuousAt (fun u : ℝ => 2 * Real.pi * u) x := by fun_prop
  have himage := mem_closure_image hc (isotropicPrimeFractions_closure hx)
  have he : 2 * Real.pi * x = α := by dsimp [x]; field_simp
  rw [he] at himage
  apply closure_mono ?_ himage
  rintro y ⟨u, ⟨r, p, hp7, hp, hr, hrp, hcop, rfl⟩, rfl⟩
  refine ⟨r, p, hp7, hp, hr, hrp, hcop, ?_⟩
  unfold isotropicPrimeAngle
  ring

theorem isotropicPrimeAngles_local_closure {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) Real.pi)
    {U : Set ℝ} (hU : IsOpen U) (hαU : α ∈ U) :
    α ∈ closure (isotropicPrimeAngles ∩ U) := by
  apply mem_closure_iff_frequently.mpr
  exact (mem_closure_iff_frequently.mp (isotropicPrimeAngles_closure hα)).and_eventually
    (hU.mem_nhds hαU)

end
end IsingBulk.AnisoF002.Isotropic
