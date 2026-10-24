import IsingBulk.Anisotropic.Geometry.CoordinateAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

private theorem cone_not_same_positive {a b alpha beta f g : ℝ}
    (_ha : 0 < a) (hb : 0 < b) (_halpha : 0 < alpha) (hbeta : 0 < beta)
    (hdet : a*b < alpha*beta) (hf : 0 < f) (hg : 0 < g)
    (h1 : g*(alpha*f-b*g) ≤ 0) (h2 : -f*(a*f-beta*g) ≤ 0) : False := by
  have hu : alpha*f-b*g ≤ 0 := nonpos_of_mul_nonpos_right h1 hg
  have hv : beta*g-a*f ≤ 0 := by
    apply nonpos_of_mul_nonpos_right (a := f) (b := beta*g-a*f) ?_ hf
    nlinarith [h2]
  have hp := mul_pos (sub_pos.mpr hdet) hf
  have hbu := mul_nonpos_of_nonneg_of_nonpos hbeta.le hu
  have hbv := mul_nonpos_of_nonneg_of_nonpos hb.le hv
  nlinarith

/-- The rectangular membership inequalities are equivalent to opposite edge signs.
The strict determinant condition excludes only the simultaneous real-angle endpoints. -/
theorem cone_inequalities_iff {a b alpha beta f g : ℝ}
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hdet : a*b < alpha*beta) :
    (g*(alpha*f-b*g) ≤ 0 ∧ -f*(a*f-beta*g) ≤ 0) ↔ f*g ≤ 0 := by
  constructor
  · rintro ⟨h1,h2⟩
    by_contra h
    have hp : 0 < f*g := lt_of_not_ge h
    rcases mul_pos_iff.mp hp with hpos | hneg
    · exact cone_not_same_positive ha hb halpha hbeta hdet hpos.1 hpos.2 h1 h2
    · apply cone_not_same_positive ha hb halpha hbeta hdet
        (neg_pos.mpr hneg.1) (neg_pos.mpr hneg.2)
      · nlinarith [h1]
      · nlinarith [h2]
  · intro h
    constructor
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos halpha.le h, mul_nonneg hb.le (sq_nonneg g)]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hbeta.le h, mul_nonneg ha.le (sq_nonneg f)]

/-- Denominator-free identities behind (2.8)--(2.10). -/
theorem edge_auxiliary_identities (h c H C t q T Q : ℝ)
    (hc : c^2-h^2=1) (hC : C^2-H^2=1) (ht : q^2+t^2=1) (hT : Q^2+T^2=1) :
    C^2*(t^2*Q^2-H^2*q^2) =
      (H^2+Q^2)*(C^2*t^2-c^2*H^2)-H^2*(c^2*T^2-h^2*C^2) ∧
    c^2*(h^2*Q^2-q^2*T^2) =
      h^2*(C^2*t^2-c^2*H^2)-(h^2+q^2)*(c^2*T^2-h^2*C^2) := by
  constructor
  · linear_combination H^2*(H^2+Q^2+T^2)*hc - H^2*(h^2+q^2+t^2)*hC -
      H^2*(H^2+1)*ht + H^2*(h^2+1)*hT
  · linear_combination h^2*(H^2+Q^2+T^2)*hc - h^2*(h^2+q^2+t^2)*hC -
      h^2*(H^2+1)*ht + h^2*(h^2+1)*hT

end
end IsingBulk.Anisotropic
