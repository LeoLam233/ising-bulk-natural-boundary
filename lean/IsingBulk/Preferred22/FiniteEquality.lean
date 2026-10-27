import IsingBulk.Preferred22.Arithmetic
import IsingBulk.Preferred22.ContourPartition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Actual full-equality product zeros and the exact prime-root arithmetic.
This classifies the potential equality singularities of the physical source;
it does not assert a bound for the complete finite complementary integral. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem preferred_root_of_unity_angle {N : ℕ} (hN : 0<N) {z : ℂ} (hz : z^N=1) :
    ∃ m : ℤ, z=IsingBulk.PrimeFamily.angleRoot N m := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨m,_,hm⟩ := (Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one hz
  refine ⟨(m:ℤ),?_⟩
  rw [← hm,← Complex.exp_nat_mul]
  unfold IsingBulk.PrimeFamily.angleRoot IsingBulk.PrimeFamily.angle
  congr 1
  push_cast
  ring

/-- A zero of the actual equal-angle product denominator forces precisely
the manuscript's integer-index Nickel equation. -/
theorem preferred_equal_product_equation {N : ℕ} (hN : 0<N) (ζ : ℂ) (l : ℤ)
    (hz : (physicalRoot (temperatureTrace ζ-
      (Real.cos (IsingBulk.PrimeFamily.angle N l):ℂ)))^N=1) :
    ∃ m : ℤ, ζ+ζ⁻¹ = (Real.cos (IsingBulk.PrimeFamily.angle N l):ℂ)+
      (Real.cos (IsingBulk.PrimeFamily.angle N m):ℂ) := by
  obtain ⟨m,hm⟩ := preferred_root_of_unity_angle hN hz
  refine ⟨m,?_⟩
  have ht := physicalRoot_trace (temperatureTrace ζ-(Real.cos (IsingBulk.PrimeFamily.angle N l):ℂ))
  rw [hm] at ht
  have ha := IsingBulk.PrimeFamily.exp_angle_add_inv (IsingBulk.PrimeFamily.angle N m)
  change IsingBulk.PrimeFamily.angleRoot N m+(IsingBulk.PrimeFamily.angleRoot N m)⁻¹=
    2*(Real.cos (IsingBulk.PrimeFamily.angle N m):ℂ) at ha
  rw [ha] at ht
  unfold temperatureTrace at ht
  linear_combination (-1/2:ℂ)*ht

theorem preferred_equal_product_implies_nickel {N : ℕ} (hN : 0<N) {ζ : ℂ}
    (hζ : ‖ζ‖=1) (l : ℤ)
    (hz : (physicalRoot (temperatureTrace ζ-
      (Real.cos (IsingBulk.PrimeFamily.angle N l):ℂ)))^N=1) :
    IsingBulk.PrimeFamily.NickelAt ζ N := by
  obtain ⟨m,hm⟩ := preferred_equal_product_equation hN ζ l hz
  exact ⟨hζ,l,m,hm⟩

/-- At genuine full equality the balanced deformation is exactly the
identity. No approximation, occupancy freezing or limiting operation enters. -/
theorem preferred_physical_product_at_equality (N : ℕ) (τ t : ℝ) (p m : ℝ → ℝ)
    (s : ℂ) :
    (∏ i : Fin N, physicalRoot (temperatureTrace s-
      Complex.cos (deformedAngles τ p m (fun _ => t) i))) =
      (physicalRoot (temperatureTrace s-(Real.cos t:ℂ)))^N := by
  simp only [deformedAngles,balancedShift_at_equality,Complex.ofReal_zero,mul_zero,sub_zero,
    ← Complex.ofReal_cos,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Every lower positive even order has a nonzero actual physical product
denominator at every constrained full-equality point, including order two. -/
theorem preferred_no_lower_equal_product {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha1 : 1≤a) (ha4 : 4*a<p) {N : ℕ} (hN : 0<N)
    (he : Even N) (hNp : N<2*p) (l : ℤ) (τ : ℝ) (u v : ℝ → ℝ) :
    1-(∏ i : Fin N, physicalRoot (temperatureTrace (IsingBulk.PrimeFamily.angleRoot p a)-
      Complex.cos (deformedAngles τ u v (fun _ => IsingBulk.PrimeFamily.angle N l) i)))≠0 := by
  intro hz
  rw [preferred_physical_product_at_equality] at hz
  have hz1 := (sub_eq_zero.mp hz).symm
  have hζ : ‖IsingBulk.PrimeFamily.angleRoot p a‖=1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hNi := preferred_equal_product_implies_nickel hN hζ l hz1
  exact (manuscript_prime_root_family hp hp5 ha1 ha4).2.1.2 N hN he hNp hNi

theorem preferred_right_equal_cosine_unique {α δ θ : ℝ}
    (hα : 0<α) (hαπ : α<Real.pi/2) (_hδ : 0≤δ) (hδα : δ<α/2)
    (hθ : θ∈Set.Icc (-Real.pi-δ) δ) (hc : Real.cos θ=Real.cos α) : θ= -α := by
  obtain ⟨k,hk⟩ := Real.cos_eq_cos_iff.mp hc.symm
  have hk0 : k=0 := by
    by_contra hk0
    rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hkle : (k:ℝ)≤-1 := by exact_mod_cast (show k≤-1 by omega)
      rcases hk with hk | hk <;> nlinarith [Real.pi_pos, hθ.1, hθ.2, mul_nonneg (by linarith : 0 ≤ -(k:ℝ)-1) Real.pi_pos.le]
    · have hkge : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
      rcases hk with hk | hk <;> nlinarith [Real.pi_pos, hθ.1, hθ.2, mul_nonneg (by linarith : 0 ≤ (k:ℝ)-1) Real.pi_pos.le]
  subst k
  simp only [Int.cast_zero,mul_zero,zero_mul,zero_add,zero_sub] at hk
  rcases hk with hk | hk
  · exfalso
    linarith [hθ.2]
  · exact hk

/-- At the first even order the actual one-sided equality singularity is
uniquely the manuscript's negative equal-angle chart. -/
theorem preferred_first_equal_product_unique {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha1 : 1≤a) (ha4 : 4*a<p) (l : ℤ) (τ δ : ℝ) (u v : ℝ → ℝ)
    (hδ : 0≤δ) (hδα : δ<IsingBulk.PrimeFamily.angle p a/2)
    (hθ : IsingBulk.PrimeFamily.angle (2*p) l∈Set.Icc (-Real.pi-δ) δ)
    (hz : (∏ i : Fin (2*p), physicalRoot (temperatureTrace (IsingBulk.PrimeFamily.angleRoot p a)-
      Complex.cos (deformedAngles τ u v (fun _ => IsingBulk.PrimeFamily.angle (2*p) l) i)))=1) :
    IsingBulk.PrimeFamily.angle (2*p) l= -IsingBulk.PrimeFamily.angle p a := by
  rw [preferred_physical_product_at_equality] at hz
  obtain ⟨m,hm⟩ := preferred_equal_product_equation (by omega : 0<2*p) _ l hz
  have ha := admissible_of_quarter_bounds hp.pos ha1 ha4
  have hc := (manuscript_prime_root_family hp hp5 ha1 ha4).2.2.1 l m hm
  exact preferred_right_equal_cosine_unique ha.1 ha.2 hδ hδα hθ hc.1

end
end IsingBulk.Preferred22
