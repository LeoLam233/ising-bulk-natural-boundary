# Two editorial clarifications to the frozen mathematical text

These clarifications apply to *The complete high-temperature Ising susceptibility: a constrained-coordinate proof of the natural boundary*, the 22-page PDF with SHA-256 `2e0e674c88f3bd5edc3846aa1f62eb2a124ce96c588221b24cc176f2a97a00d9` and TeX with SHA-256 `5d962d44180f33df66fbad90e2f66a8c95425d3eddc91765abb6953bd3b48c0f`.

## 1. Section 6, regularity of the bordered pair kernel

On page 9, in the paragraph preceding equation (6.5), the phrase

> the double lower branch is the only limiting pair-product zero on the one-sided support

means

> the double lower branch is the only limiting zero of the pair denominator \(1-z_i z_l\) on the one-sided support.

The pair product itself also vanishes on ordinary collision diagonals. The paragraph is proving that the bordered kernel has no remaining pole. At the double lower branch, the even inverse in \(\varphi\) supplies the numerator factor \(\varphi_i+\varphi_l\) that cancels the vanishing denominator. Away from that point the denominator is separated. The diagonal factor \(v_i-v_l\) remains, exactly as used in the following displayed estimate. No estimate or domain is changed by this clarification.

## 2. Lemma 7.2, dependence on the fixed derivative order

In Lemma 7.2, equations (7.12) and (7.13) on page 14, the constants written \(C_j N^{C_j}\) depend on the fixed total derivative order \(m=a+|\beta|\). They may be written \(C_m N^{C_m}\). Equivalently, after fixing any finite derivative budget \(j\), the displayed estimates hold for every \(m\le j\), with constants \(C_j\).

Thus the statement is

\[
 |\partial_t^a\partial_v^\beta B_i|
 +|\partial_t^a\partial_v^\beta V_i|
 \le C_m N^{C_m}\Delta^{-1-m},
 \qquad m=a+|\beta| \text{ fixed}.
\]

The corresponding bounds for \(R\), \(R^{-1}\) and \(G_i\) have the same fixed-order convention. The proof already uses bounded analytic jets and the quotient rule at each fixed order. No constant uniform over arbitrarily large derivative orders is asserted or needed. All applications first fix the finite order \(k=(p^2-1)/2\) and the finite jet budget required by its transport recurrence.

These are wording and index clarifications. They add no hypothesis, lemma, estimate, particle restriction, or mathematical repair. The delivered PDF and TeX retain their exact reviewed bytes; this separate record makes the intended fixed-order statement explicit.
