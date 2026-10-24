import IsingBulk.Anisotropic.RegularEdges.LeadingDerivative
import IsingBulk.First.ShapeLowerOrderBounds

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set Filter Metric
open scoped Topology BigOperators

theorem shapeVandermondeSq_le_norm_power {n : ℕ} (x : ShapeSpace n) :
    shapeVandermondeSq x≤(2*‖x‖)^((n+1)*n) := by
  calc
    shapeVandermondeSq x=∏ p∈firstStrictPairs (n+1),(x.1 p.1-x.1 p.2)^2 := by
      simp [shapeVandermondeSq,firstVandermonde,Finset.prod_pow]
    _ ≤ ∏ _p∈firstStrictPairs (n+1),(2*‖x‖)^2 := by
      apply Finset.prod_le_prod₀ (fun p _ => sq_nonneg _)
      intro p _
      have h1 := PiLp.norm_apply_le x.1 p.1
      have h2 := PiLp.norm_apply_le x.1 p.2
      rw [Real.norm_eq_abs] at h1 h2
      change |x.1 p.1|≤‖x‖ at h1
      change |x.1 p.2|≤‖x‖ at h2
      have hh := (abs_sub (x.1 p.1) (x.1 p.2)).trans (add_le_add h1 h2)
      nlinarith [sq_abs (x.1 p.1-x.1 p.2),abs_nonneg (x.1 p.1-x.1 p.2),norm_nonneg x]
    _ = _ := by rw [Finset.prod_const,←pow_mul,firstStrictPairs_twice_card]

/-- Above the Vandermonde threshold even the local derivative integrand is uniformly bounded. -/
theorem norm_high_shapeQuotient_le {n j : ℕ} (hn : 1≤n)
    (hdegree : 2*(j+1)≤(n+1)*n) {M c : ℝ} (hM : 0≤M) (hc : 0<c)
    (x : ShapeSpace n) (hx : ‖x‖≤1) (A D : ℂ) (hA : ‖A‖≤M)
    (hD : c*‖x‖^2≤‖D‖) :
    ‖(shapeVandermondeSq x:ℂ)*A/D^(j+1)‖≤2^((n+1)*n)*M/c^(j+1) := by
  by_cases hx0 : x=0
  · subst x
    simp only [shapeVandermondeSq_zero hn,Complex.ofReal_zero,zero_mul,zero_div,norm_zero]
    positivity
  have hp : 0<‖x‖ := norm_pos_iff.mpr hx0
  have hpoly : shapeVandermondeSq x≤2^((n+1)*n)*‖x‖^(2*(j+1)) := by
    calc
      _ ≤ (2*‖x‖)^((n+1)*n) := shapeVandermondeSq_le_norm_power x
      _ = 2^((n+1)*n)*‖x‖^((n+1)*n) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (norm_nonneg _) hx hdegree) (by positivity)
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (shapeVandermondeSq_nonneg x),norm_pow]
  calc
    _ ≤ (2^((n+1)*n)*‖x‖^(2*(j+1))*M)/(c*‖x‖^2)^(j+1) := by
      apply div_le_div₀
      · positivity
      · exact mul_le_mul hpoly hA (norm_nonneg _) (by positivity)
      · positivity
      · exact pow_le_pow_left₀ (by positivity) hD _
    _ = _ := by
      rw [mul_pow,pow_mul]
      field_simp
      simp only [pow_mul]
      ring

theorem edge_higher_derivative_pointwise_bound {n j : ℕ} (hn : 1≤n)
    (hdegree : 2*(j+1)≤(n+1)*n) {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∃ r δ C : ℝ,0<r ∧ 0<δ ∧ 0≤C ∧ ∀ t : ℝ,0<t → t<δ →
      ∀ x : ShapeSpace n,‖x‖<r →
        ‖iteratedDeriv j (fun u => edgeAngularDensity b B S u (fun i => x.1 i))
          (Complex.I*(t:ℂ)^2)‖≤C := by
  obtain ⟨R,M,hR,hRπ,hM,hlocal⟩ := edgeShape_local_bounds (n := n) hb hB hBi hS hS0 j
  obtain ⟨r,hr,hid⟩ := edgeShape_derivative_neighborhood (n := n) hb hB hBi hS hS0
  obtain ⟨c,δ,hc,hδ,hgap⟩ := edgeShapeDenominator_gap (n := n) (b := b) hBi hB.continuousAt
  let L := min 1 (min R r)
  have hL : 0<L := lt_min zero_lt_one (lt_min hR hr)
  have hLR : L≤R := (min_le_right _ _).trans (min_le_left _ _)
  have hLr : L≤r := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨L,min L δ,2^((n+1)*n)*M/c^(j+1),hL,lt_min hL hδ,by positivity,?_⟩
  intro t ht htδ x hx
  have htL : t<L := htδ.trans_le (min_le_left _ _)
  have htr : |t|<r := by rw [abs_of_pos ht]; exact htL.trans_le hLr
  have htR : |t|<R := by rw [abs_of_pos ht]; exact htL.trans_le hLR
  have hangle (i : Fin (n+1)) : x.1 i∈Icc (-Real.pi) Real.pi := by
    have hh := PiLp.norm_apply_le x.1 i
    rw [Real.norm_eq_abs] at hh
    have hp : |x.1 i|<Real.pi := hh.trans_lt (hx.trans_le (hLR.trans hRπ))
    exact ⟨(abs_lt.mp hp).1.le,(abs_lt.mp hp).2.le⟩
  have hg := hgap t ht (htδ.trans_le (min_le_right _ _)) x hangle
  have hne : edgeShapeDenominator b B t x≠0 := by
    intro he
    rw [he,norm_zero] at hg
    have hp : 0<c*(t^2+‖x‖^2) := by positivity
    linarith
  rw [hid t htr x (hx.trans_le hLr) hne j]
  apply norm_high_shapeQuotient_le hn hdegree hM hc x
    (hx.le.trans (min_le_left _ _)) _ _
    ((hlocal t htR).2.2 x (by simpa using hx.trans_le hLR))
  nlinarith [mul_nonneg hc.le (sq_nonneg t)]

end
end IsingBulk.Anisotropic.RegularEdges
