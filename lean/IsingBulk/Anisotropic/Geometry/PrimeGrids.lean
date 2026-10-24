import IsingBulk.Anisotropic.Geometry.CandidateClosure
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Floor.Ring

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

def primeRationalGrid : Set (ℝ × ℝ) :=
  {xy | ∃p : ℕ, p.Prime ∧ Odd p ∧ ∃j k : ℤ, xy=((j:ℝ)/p,(k:ℝ)/p)}

theorem floor_div_approx {p : ℝ} (hp : 0<p) (x : ℝ) :
    |((⌊p*x⌋:ℤ):ℝ)/p-x|<1/p := by
  have h1 := Int.floor_le (p*x)
  have h2 := Int.lt_floor_add_one (p*x)
  have hle : ((⌊p*x⌋:ℤ):ℝ)/p≤x := (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h1)
  have hlt : x<((⌊p*x⌋:ℤ):ℝ)/p+1/p := by
    rw [←add_div,lt_div_iff₀ hp]
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

/-- Simultaneous rational meshes with an odd prime denominator are dense in the plane. -/
theorem primeRationalGrid_dense : Dense primeRationalGrid := by
  intro xy
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  rcases exists_nat_gt (1/ε) with ⟨N,hN⟩
  rcases Nat.exists_infinite_primes (max (N+1) 3) with ⟨p,hp,hprime⟩
  have hpN : N<p := by omega
  have hp3 : 3≤p := by omega
  have hp0 : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hsmall : 1/(p:ℝ)<ε := by
    rw [div_lt_iff₀ hp0]
    have hn : (1:ℝ)/ε<(p:ℝ) := hN.trans (by exact_mod_cast hpN)
    have hm := (div_lt_iff₀ hε).mp hn
    nlinarith
  let j : ℤ := ⌊(p:ℝ)*xy.1⌋
  let k : ℤ := ⌊(p:ℝ)*xy.2⌋
  refine ⟨((j:ℝ)/p,(k:ℝ)/p),⟨p,hprime,hprime.odd_of_ne_two (by omega),j,k,rfl⟩,?_⟩
  rw [Prod.dist_eq,max_lt_iff]
  constructor
  · simpa only [Real.dist_eq,abs_sub_comm,j] using (floor_div_approx hp0 xy.1).trans hsmall
  · simpa only [Real.dist_eq,abs_sub_comm,k] using (floor_div_approx hp0 xy.2).trans hsmall

def cosineGridMap (d : ℝ) (xy : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos (2*Real.pi*xy.1/d),Real.cos (2*Real.pi*xy.2/d))

def primeCosineGrid (d : ℝ) : Set (ℝ × ℝ) := cosineGridMap d '' primeRationalGrid

theorem cosineGridMap_continuous (d : ℝ) : Continuous (cosineGridMap d) := by
  unfold cosineGridMap
  fun_prop

theorem primeCosineGrid_subset_square (d : ℝ) : primeCosineGrid d⊆cosineSquare := by
  rintro xy ⟨uv,_,rfl⟩
  exact ⟨⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩,⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩⟩

theorem square_subset_closure_primeCosineGrid {d : ℝ} (hd : d≠0) :
    cosineSquare⊆closure (primeCosineGrid d) := by
  rintro uv ⟨hu,hv⟩
  let xy : ℝ × ℝ := (d*Real.arccos uv.1/(2*Real.pi),d*Real.arccos uv.2/(2*Real.pi))
  have he : cosineGridMap d xy=uv := by
    apply Prod.ext
    · change Real.cos (2*Real.pi*(d*Real.arccos uv.1/(2*Real.pi))/d)=uv.1
      have ha : 2*Real.pi*(d*Real.arccos uv.1/(2*Real.pi))/d=Real.arccos uv.1 := by
        field_simp [hd,Real.pi_ne_zero]
      rw [ha,Real.cos_arccos hu.1 hu.2]
    · change Real.cos (2*Real.pi*(d*Real.arccos uv.2/(2*Real.pi))/d)=uv.2
      have ha : 2*Real.pi*(d*Real.arccos uv.2/(2*Real.pi))/d=Real.arccos uv.2 := by
        field_simp [hd,Real.pi_ne_zero]
      rw [ha,Real.cos_arccos hv.1 hv.2]
  rw [←he]
  have hm : Set.MapsTo (cosineGridMap d) primeRationalGrid (primeCosineGrid d) :=
    fun _ hx => Set.mem_image_of_mem _ hx
  exact hm.closure (cosineGridMap_continuous d) (primeRationalGrid_dense xy)

theorem closure_prime_candidateSet (lam : ℝ) {d : ℝ} (hd : d≠0) :
    closure (candidateSet lam (primeCosineGrid d))=spectralSet lam :=
  closure_candidateSet_eq_spectralSet lam (primeCosineGrid_subset_square d)
    (square_subset_closure_primeCosineGrid hd)

/-- Odd prime orders alone already have the full spectral closure. -/
theorem closure_odd_prime_candidates (lam : ℝ) :
    closure (candidateSet lam (primeCosineGrid 1))=spectralSet lam :=
  closure_prime_candidateSet lam one_ne_zero

/-- Even orders twice an odd prime alone already have the full spectral closure. -/
theorem closure_even_prime_candidates (lam : ℝ) :
    closure (candidateSet lam (primeCosineGrid 2))=spectralSet lam :=
  closure_prime_candidateSet lam (by norm_num)

end
end IsingBulk.Anisotropic
