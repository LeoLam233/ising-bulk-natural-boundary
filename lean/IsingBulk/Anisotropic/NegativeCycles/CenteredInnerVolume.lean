import IsingBulk.Anisotropic.NegativeCycles.CenteredWitnessRemainder
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory
open scoped BigOperators

theorem centeredInnerCompact_subset_box (n : ℕ) (d s L : ℝ) (hL : 0≤L) (hs : s≤L^2) :
    centeredInnerCompact n d s⊆Icc (fun _=>-L) (fun _=>L) := by
  intro q hq
  have hq' : constrainedSquaredRadius q≤L^2 := by
    change constrainedSquaredRadius q≤s-(n+1:ℕ)*d^2 at hq
    have hn : 0≤(n+1:ℕ)*(d^2:ℝ) := by positivity
    linarith
  have hh := (constrainedSquaredRadius_coordinates_le q hL hq').1
  exact ⟨fun i=>(abs_le.mp (hh i)).1,fun i=>(abs_le.mp (hh i)).2⟩

theorem centeredInnerSet_subset_box (n : ℕ) (d s L : ℝ) (hL : 0≤L) (hs : s≤L^2) :
    centeredInnerSet n d s⊆Icc (fun _=>-L) (fun _=>L) :=
  (centeredInnerSet_subset_compact n d s).trans (centeredInnerCompact_subset_box n d s L hL hs)

theorem centeredInnerSet_volume_bound (n : ℕ) (d s L : ℝ) (hL : 0≤L) (hs : s≤L^2) :
    (volume (centeredInnerSet n d s)).toReal≤(2*L)^n := by
  have hm := measureReal_mono (μ := volume) (centeredInnerSet_subset_box n d s L hL hs)
    isCompact_Icc.measure_lt_top.ne
  have hb : (volume (Icc (fun _ : Fin n=>-L) (fun _=>L))).toReal=(2*L)^n := by
    rw [Real.volume_Icc_pi_toReal (by intro i; linarith)]
    simp only [sub_neg_eq_add,←two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simpa only [measureReal_def,hb] using hm

theorem centeredInnerSet_volume_ne_top (n : ℕ) (d s : ℝ) :
    volume (centeredInnerSet n d s)≠⊤ :=
  ne_top_of_le_ne_top (centeredInnerCompact_isCompact n d s).measure_lt_top.ne
    (measure_mono (centeredInnerSet_subset_compact n d s))

/-- The exact sector-count factor is retained when a common envelope is summed
only over active winding sectors. -/
theorem centeredInnerSet_sector_sum_bound (n : ℕ) (A : Finset (Fin (n+2)))
    (d : Fin (n+2)→ℝ) (s L E : ℝ) (hL : 0≤L) (hs : s≤L^2) (hE : 0≤E)
    (F : A→ℂ) (hF : ∀k,‖F k‖≤(volume (centeredInnerSet n (d k) s)).toReal*E) :
    ‖∑k,F k‖≤(n+2:ℕ)*(2*L)^n*E := by
  have hpoint (k : A) : ‖F k‖≤(2*L)^n*E :=
    (hF k).trans (mul_le_mul_of_nonneg_right (centeredInnerSet_volume_bound n (d k) s L hL hs) hE)
  have hh := (norm_sum_le (Finset.univ : Finset A) F).trans
    (Finset.sum_le_sum (fun k _=>hpoint k))
  have hcard : Fintype.card A≤n+2 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun k : A=>(k:Fin (n+2))) Subtype.val_injective
  have hm := mul_le_mul_of_nonneg_right (show (Fintype.card A:ℝ)≤n+2 by exact_mod_cast hcard)
    (show 0≤(2*L)^n*E by positivity)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  exact hh.trans (by simpa only [Nat.cast_add,Nat.cast_ofNat,mul_assoc] using hm)

/-- The literal remainder sum keeps one and the same R₀ for every active sector.
The individual bounds are exactly those returned by exists_centered_witness_remainder. -/
theorem centered_remainder_sector_sum_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (R₀ : ℂ→ℂ) (m j : ℕ) (A : Finset (Fin (2*m+2)))
    (d : Fin (2*m+2)→ℝ) (T : A→Config (2*m+1)→ℂ)
    (s L K M c : ℝ) (hL : 0≤L) (hs : s≤L^2) (hK : 0≤K) (hM : 0≤M) (hc : 0<c)
    (hbound : ∀k : A,
      ‖iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k)) 0/(j.factorial:ℂ)‖≤
        ((volume (centeredInnerSet (2*m) (d k) s)).toReal*(K*remainderGaussianEnvelope M m))/
          ((c/(2*m+1:ℕ))/2)^j) :
    ‖∑k : A,iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k)) 0/(j.factorial:ℂ)‖≤
      ((2*m+2:ℕ)*(2*L)^(2*m)*(K*remainderGaussianEnvelope M m))/((c/(2*m+1:ℕ))/2)^j := by
  have hE : 0≤(K*remainderGaussianEnvelope M m)/((c/(2*m+1:ℕ))/2)^j := by
    unfold remainderGaussianEnvelope
    positivity
  have hh := centeredInnerSet_sector_sum_bound (2*m) A d s L
    ((K*remainderGaussianEnvelope M m)/((c/(2*m+1:ℕ))/2)^j) hL hs hE
    (fun k=>iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (d k) s (T k)) 0/(j.factorial:ℂ))
    (fun k=>by simpa only [mul_div_assoc] using hbound k)
  simpa only [mul_div_assoc] using hh

end IsingBulk.Anisotropic.NegativeCycles
