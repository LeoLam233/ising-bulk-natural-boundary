import IsingBulk.First.OnsiteGlobalBound
import IsingBulk.First.OnsiteRadiusIndependence
import IsingBulk.First.NormalizationDerivatives
import IsingBulk.First.PublishedFixedOrder
import IsingBulk.First.MeanSelectedData
import IsingBulk.First.NonNickelRadialBounds

/-! The published full-site transfer is retained as a historical comparison.
The selected lower-order endpoint now uses the internal offsite radial proof. -/
namespace IsingBulk.First
noncomputable section
open Set
open scoped Topology

theorem lowerOrder_radial_bound_of_published (N : ℕ) (hN : 0 < N)
    (level : ℝ) (hlevel : 0 < level ∧ level < 2) (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ:ℂ)*Complex.I)) = (level:ℂ))
    (hTW : PublishedFullSiteBounded N (Complex.exp ((θ:ℂ)*Complex.I))) :
    ∀ j : ℕ, ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖(deriv^[j] (upperFormFactor N)) (IsingBulk.Branch.radialParameter θ ε)‖ ≤ C := by
  obtain ⟨eO,heO,hO⟩ := onsite_global_radial_bound hN level hlevel θ hθ hS
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  intro j
  obtain ⟨δ,Cs,hδ,hCs,hpub⟩ := hTW j
  obtain ⟨Co,hCo,honsite⟩ := hO j
  let ε₀ := min δ (min eO d)
  refine ⟨ε₀,(Cs+Co)/2,(lt_min hδ (lt_min heO hd)),by positivity,?_⟩
  intro ε hε hεsmall
  have hεδ : ε < δ := hεsmall.trans_le (min_le_left _ _)
  have hεO : ε ≤ eO := hεsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd : ε < d := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let s := IsingBulk.Branch.radialParameter θ ε
  let r := (sourceRadialPair θ ε).1
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) hε
  have hmr : r⁻¹-r < (sourceS s).im := by
    have hnear : ‖s-IsingBulk.Branch.radialParameter θ ε‖ < (Real.sin θ/16)*ε := by
      simpa only [s,sub_self,norm_zero] using
        (mul_pos (show 0 < Real.sin θ/16 by positivity) hε)
    exact (hm ε hε hεd s hnear).2
  have hsd : ‖s-Complex.exp ((θ:ℂ)*Complex.I)‖ < δ := by
    have heq : s-Complex.exp ((θ:ℂ)*Complex.I) = (ε:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) := by
      dsimp [s, IsingBulk.Branch.radialParameter]
      push_cast
      ring
    rw [heq,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hε]
    exact hεδ
  have hsout : 1 < ‖s‖ := by
    rw [show s = IsingBulk.Branch.radialParameter θ ε from rfl,radialParameter_norm hε.le]
    linarith
  obtain ⟨r₀,hr₀,hr₀1,hstd⟩ := hpub s hsd hsout
  let R := (max r r₀+1)/2
  have hm1 : max r r₀ < 1 := max_lt hr1 hr₀1
  have hmR : max r r₀ < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hrR : r ≤ R := (le_max_left _ _).trans hmR.le
  have hR : 0 < R := hr.trans_le hrR
  have hr₀R : r₀ < R := (le_max_right _ _).trans_lt hmR
  have hinv : R⁻¹ ≤ r⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hr hrR
  have hmarginR : R⁻¹-R < (sourceS s).im := by linarith
  have hCstd : ‖iteratedDeriv j (standardFormFactor N R) s‖ ≤ Cs := by
    simpa only [iteratedDeriv_eq_iterate] using hstd R hr₀R hR1
  have hCons : ‖iteratedDeriv j (onsiteFormFactor N R) s‖ ≤ Co := by
    rw [onsiteFormFactor_iteratedDeriv_radius_eq N hN j hr hR1 hrR hmr]
    simpa only [iteratedDeriv_eq_iterate,r,s,sourceRadialPair] using honsite ε hε hεO
  rw [← iteratedDeriv_eq_iterate]
  exact (upperFormFactor_iteratedDeriv_norm_bound N hN j hR hR1 hmarginR).trans (by linarith)

/-- Prime-family arithmetic and the internal non-Nickel radial bound supply
the lower-order endpoint, with fixed-radius locality transferred internally. -/
theorem selected_lower_orders_radial_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) :
    ∀ N : ℕ, 0 < N → Even N → N < 2*p → ∀ j : ℕ,
      ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖(deriv^[j] (upperFormFactor N))
          (IsingBulk.Branch.radialParameter (selectedOrderedChart ha hb).theta ε)‖ ≤ C := by
  intro N hN he hlt j
  have hlevel := PrimeFamily.cosineAverage_bounds ha hb
  have hS : sourceS (Complex.exp (((selectedOrderedChart ha hb).theta:ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,selectedOrderedChart,
      Complex.ofReal_mul,Complex.ofReal_ofNat] using PrimeFamily.selectedPoint_relation ha hb
  have hn := (PrimeFamily.first_even_Nickel_order hp (by omega) ha hb).2 N hN he hlt
  obtain ⟨e,he0,hbnd⟩ := nonNickel_fixed_radius_radial_bound hN
    (2*PrimeFamily.cosineAverage p a b) (selectedOrderedChart ha hb).theta
    (by constructor <;> linarith) (selectedOrderedChart ha hb).sin_theta_pos hS hn
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin (selectedOrderedChart ha hb).sin_theta_pos
  obtain ⟨C,hC,hB⟩ := hbnd j
  refine ⟨min e d,C,lt_min he0 hd,hC,?_⟩
  intro ε hε hεsmall
  have hεe := hεsmall.trans_le (min_le_left e d)
  have hεd := hεsmall.trans_le (min_le_right e d)
  have hmargin := (hm ε hε hεd (IsingBulk.Branch.radialParameter (selectedOrderedChart ha hb).theta ε)
    (by simpa using mul_pos (show 0 < Real.sin (selectedOrderedChart ha hb).theta/16 by
      positivity [(selectedOrderedChart ha hb).sin_theta_pos]) hε)).2
  have hr : 0 < (sourceRadialPair (selectedOrderedChart ha hb).theta ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair (selectedOrderedChart ha hb).theta ε).1 < 1 := by
    change Real.exp (-(Real.sin (selectedOrderedChart ha hb).theta/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith [(selectedOrderedChart ha hb).sin_theta_pos]) hε
  rw [← iteratedDeriv_eq_iterate,
    upperFormFactor_iteratedDeriv_fixed_radius N hN j hr hr1
      (s := IsingBulk.Branch.radialParameter (selectedOrderedChart ha hb).theta ε) hmargin,
    iteratedDeriv_eq_iterate]
  exact hB ε hε hεe.le


end
end IsingBulk.First
