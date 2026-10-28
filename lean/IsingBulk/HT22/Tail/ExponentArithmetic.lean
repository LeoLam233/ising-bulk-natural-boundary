import IsingBulk.HT.First.OrderArithmetic

/-! F001 exact improved shell exponent. The existing odd-order arithmetic
is reused, but the old N²−2j−4 tail estimate is not substituted. -/
namespace IsingBulk.HT22
open IsingBulk.HT.First

theorem full_shell_exponent {p N j : ℕ} (hp : Odd p)
    (hN : p+2 ≤ N) (hj : j ≤ derivativeOrder p) :
    4*p+2 ≤ N^2-2*j-3 := by
  have horder := odd_square_order hp
  have hs : (p+2)^2 ≤ N^2 := Nat.pow_le_pow_left hN 2
  have hlarge : 4*p+2+2*j+3 ≤ N^2 := by nlinarith
  omega

theorem full_shell_exponent_pos {p N j : ℕ} (hp : Odd p)
    (hN : p+2 ≤ N) (hj : j ≤ derivativeOrder p) :
    0 < N^2-2*j-3 := by
  have := full_shell_exponent hp hN hj
  omega

/-- The N−2 ordinary interval factors and one extreme-coordinate coarea
factor leave Δ^(N−3), not a second independent coarea variable. -/
theorem density_plus_coarea_exponent {N j : ℕ}
    (hN : 3 ≤ N) (hj : 2*j ≤ N*(N-1)) :
    (N*(N-1)-2*j)+(N-3)=N^2-2*j-3 := by
  have hsub : N-1+1=N := by omega
  have hsub3 : N-3+3=N := by omega
  have hdegree : N*(N-1)+N=N^2 := by nlinarith
  omega

end IsingBulk.HT22
