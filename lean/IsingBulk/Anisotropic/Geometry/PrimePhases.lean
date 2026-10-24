import IsingBulk.Anisotropic.Geometry.PrimeGrids
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

def primeInteriorFractions : Set ℝ :=
  {x | ∃p k : ℕ, p.Prime ∧ Odd p ∧ 0<k ∧ 2*k<p ∧ x=(k:ℝ)/p}

def primePhaseCosines : Set ℝ :=
  (fun x : ℝ => Real.cos (2*Real.pi*x)) '' primeInteriorFractions

theorem interior_subset_closure_primeFractions : Set.Ioo (0:ℝ) (1/2)⊆closure primeInteriorFractions := by
  intro x hx
  apply mem_closure_iff.mpr
  intro N hN hxN
  let V : Set (ℝ × ℝ) := Prod.fst ⁻¹' (N∩Set.Ioo (0:ℝ) (1/2))
  have hV : IsOpen V := (hN.inter isOpen_Ioo).preimage continuous_fst
  rcases mem_closure_iff.mp (primeRationalGrid_dense (x,0)) V hV ⟨hxN,hx⟩ with ⟨uv,huv,hgrid⟩
  rcases hgrid with ⟨p,hp,ho,j,k,he⟩
  subst uv
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hjr : (0:ℝ)<j := (div_pos_iff_of_pos_right hp0).mp huv.2.1
  have hj : (0:ℤ)<j := by exact_mod_cast hjr
  have hjp : 2*j<(p:ℤ) := by
    have h := (div_lt_iff₀ hp0).mp huv.2.2
    have hr : 2*(j:ℝ)<(p:ℝ) := by linarith
    exact_mod_cast hr
  have hcast : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj.le
  refine ⟨(j:ℝ)/p,huv.1,p,j.toNat,hp,ho,?_,?_,?_⟩
  · exact_mod_cast (hcast.symm ▸ hj)
  · exact_mod_cast (hcast.symm ▸ hjp)
  · congr 1
    exact_mod_cast hcast.symm

/-- Prime primitive phases with 1≤k≤(p−1)/2 give dense cosine coordinates on every edge interval. -/
theorem interior_subset_closure_primePhaseCosines : Set.Ioo (-1:ℝ) 1⊆closure primePhaseCosines := by
  intro b hb
  let x := Real.arccos b/(2*Real.pi)
  have hp : 0<2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hx : x∈Set.Ioo (0:ℝ) (1/2) := by
    constructor
    · exact div_pos (Real.arccos_pos.mpr hb.2) hp
    · apply (div_lt_iff₀ hp).mpr
      have h := Real.arccos_lt_pi.mpr hb.1
      linarith
  have hm : Set.MapsTo (fun x : ℝ => Real.cos (2*Real.pi*x)) primeInteriorFractions primePhaseCosines :=
    fun _ hx => Set.mem_image_of_mem _ hx
  have hc : Continuous (fun x : ℝ => Real.cos (2*Real.pi*x)) := by fun_prop
  have h := hm.closure hc (interior_subset_closure_primeFractions hx)
  have he : Real.cos (2*Real.pi*x)=b := by
    dsimp [x]
    rw [mul_div_cancel₀ _ hp.ne',Real.cos_arccos hb.1.le hb.2.le]
  change Real.cos (2*Real.pi*x)∈closure primePhaseCosines at h
  rwa [he] at h

def primePhase (p k : ℕ) : ℝ := 2*Real.pi*k/p

def primePhaseRoot (p k : ℕ) : ℂ := Complex.exp (-Complex.I*(primePhase p k:ℂ))

theorem mem_primePhaseCosines_iff (b : ℝ) : b∈primePhaseCosines ↔
    ∃p k : ℕ, p.Prime ∧ Odd p ∧ 0<k ∧ 2*k<p ∧ b=Real.cos (primePhase p k) := by
  constructor
  · rintro ⟨x,⟨p,k,hp,ho,hk,hkp,rfl⟩,rfl⟩
    refine ⟨p,k,hp,ho,hk,hkp,?_⟩
    change Real.cos (2*Real.pi*((k:ℝ)/p))=Real.cos (2*Real.pi*k/p)
    congr 1
    ring
  · rintro ⟨p,k,hp,ho,hk,hkp,rfl⟩
    refine ⟨(k:ℝ)/p,⟨p,k,hp,ho,hk,hkp,rfl⟩,?_⟩
    change Real.cos (2*Real.pi*((k:ℝ)/p))=Real.cos (2*Real.pi*k/p)
    congr 1
    ring

theorem primePhase_bounds {p k : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : 2*k<p) :
    0<primePhase p k ∧ primePhase p k<Real.pi := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hkp' : (2:ℝ)*k<p := by exact_mod_cast hkp
  constructor
  · unfold primePhase
    positivity
  · unfold primePhase
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]

theorem primePhaseRoot_isPrimitiveRoot {p k : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : k<p) :
    IsPrimitiveRoot (primePhaseRoot p k) p := by
  have hc : k.Coprime p := ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hk hkp)).symm
  have h := (Complex.isPrimitiveRoot_exp_of_coprime k p hp.ne_zero hc).inv
  have he : -Complex.I*(primePhase p k:ℂ)= -(2*(Real.pi:ℂ)*Complex.I*((k:ℂ)/p)) := by
    unfold primePhase
    push_cast
    ring
  unfold primePhaseRoot
  rw [he,Complex.exp_neg]
  exact h

theorem primePhaseRoot_pow_eq_one_iff {p k N : ℕ} (hp : p.Prime) (hk : 0<k) (hkp : k<p) :
    primePhaseRoot p k^N=1 ↔ p∣N :=
  (primePhaseRoot_isPrimitiveRoot hp hk hkp).pow_eq_one_iff_dvd N


theorem primePhaseRoot_first_positive_odd {p k : ℕ} (hp : p.Prime) (ho : Odd p)
    (hk : 0<k) (hkp : k<p) :
    Odd p ∧ primePhaseRoot p k^p=1 ∧
    ∀N : ℕ, 0<N → N<p → primePhaseRoot p k^N≠1 := by
  refine ⟨ho,(primePhaseRoot_isPrimitiveRoot hp hk hkp).pow_eq_one,?_⟩
  intro N hN hNp h
  exact (not_le_of_gt hNp) (Nat.le_of_dvd hN ((primePhaseRoot_pow_eq_one_iff hp hk hkp).mp h))

theorem primePhaseRoot_even_resonance_iff {p k N : ℕ} (hp : p.Prime) (ho : Odd p)
    (hk : 0<k) (hkp : k<p) (hN : Even N) :
    primePhaseRoot p k^N=1 ↔ 2*p∣N := by
  rw [primePhaseRoot_pow_eq_one_iff hp hk hkp]
  constructor
  · intro hd
    exact (Nat.coprime_two_left.mpr ho).mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp hN) hd
  · exact fun h => dvd_trans (dvd_mul_left p 2) h

theorem primePhaseRoot_first_positive_even {p k : ℕ} (hp : p.Prime) (ho : Odd p)
    (hk : 0<k) (hkp : k<p) :
    Even (2*p) ∧ primePhaseRoot p k^(2*p)=1 ∧
    ∀N : ℕ, Even N → 0<N → N<2*p → primePhaseRoot p k^N≠1 := by
  have he : Even (2*p) := even_two_mul p
  refine ⟨he,(primePhaseRoot_even_resonance_iff hp ho hk hkp he).mpr dvd_rfl,?_⟩
  intro N hN hpos hlt h
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((primePhaseRoot_even_resonance_iff hp ho hk hkp hN).mp h))

end
end IsingBulk.Anisotropic
