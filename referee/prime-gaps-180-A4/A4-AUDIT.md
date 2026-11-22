# A4 audit: "Infinitely Many Small Prime Gaps of 180 or Less" (Allahyar and Yianni, 21 Nov 2026)

Prepared for Pablo Nogueira Grossi (G6 LLC). Checks by Claude Sonnet 5.5, 22 Nov 2026. Internal, report-only. **Nothing here has been sent to the authors or published. No repository was changed and nothing was compiled.** Independent of the Euler/Hecke/AXLE work and of the Lean RH audit. No verdict on the truth of A4 or of the theorem is implied.

**Status: PARTIALLY RESOLVED. A4 unestablished; no defect demonstrated by the bounded investigation.** This is a bounded source-and-numerical audit record, not a proof or disproof of A4 and not a completed mathematical review. The small-prime values of Ŵ(0,0)/p³ below are not asymptotic estimates.

**Priorities for a specialist:**
1. Exceptional geometry: can the argument excluding exceptional curves be justified uniformly in all parameters?
2. Type III transfer: does the exceptional-frequency contribution stay controlled after the Type III weighting and the residual-length extension?
3. Formal fidelity: does `HasFiniteExceptionalTypeIIIInput` express exactly the analytic statement in A4, with no extra assumption hidden in the interface?

## Scope read, and not read
- Read: the 34-page PDF supplied. Pages 2–3 (A1–A4 and the definitions of C, K, W, Ŵ) were read from the page images. Read as text: Sections 1, 2, 3 (partly), 4 (4.3–4.7), 5.1–5.4, 6.6 and 6.2 remark, 7, 8.1, 9, Appendix A, Appendix B's list, and the reference list.
- **Not read:** Section 4.8–4.9, most of Section 6, Appendix C, Appendix B's tail, and the upstream sources [9] (Sharifi/GPT-6 Astra, "Kloosterman correlations with finitely many exceptional Fourier frequencies"), [22] (fixed-profile 182 paper), [23] (Lean repository, commit b77bf175bded) and [18] (OpenAI 186 repository). They are web-hosted and were not fetched; downloading was not authorised. **The Lean source of `HasFiniteExceptionalTypeIIIInput` was not seen**, only its name and the paper's one-line faithfulness remark.
- Provenance as stated by the authors: [9], [22], [23] are AI-generated (GPT-6 Astra, prompted by R. Sharifi); the paper says the proof of A4 in [9] has not been refereed.

## 1. Exact statement of A4 (question 1)

**Established (transcribed from the page image; internally consistent as written).**
Kl3(t) = p⁻¹ Σ_{u,v∈F_p^×} e_p(u+v+t/(uv)).
C(A,B) = Σ_{h≠0} Kl3(Ah) · conj Kl3(Bh) · e_p(h).
K_{m,n}(r1,r2) = C(α r2/(m r1²), α r1/(n r2²)) for r1 r2 ≠ 0, and 0 otherwise.
W = K_{m,n} · conj K_{m',n} · K_{m',n'} · conj K_{m,n'}, and Ŵ(h,k) = Σ_{r1,r2∈F_p} W(r1,r2) e_p(h r1 + k r2).
A4: there exist C4>0, D4∈ℕ, p0 such that for all primes p>p0 and all α,m,m',n,n'∈F_p^×:
- (1) if m≠m' and n≠n': there is Z⊂F_p² with |Z|≤D4 and |Ŵ| ≤ C4 p³(1+√p·1_Z).
- (2) otherwise: there is a nonzero polynomial P of degree ≤D4 with |Ŵ| ≤ C4 p³(1+√p·1_{P=0}+p·1_{(h,k)=(0,0)}).

Properties I checked from the displayed definitions (algebra by hand, then numerically at p=7 and 13, agreement to ~1e-13):
- The definition is well posed: all parameters are nonzero, K vanishes when r1r2=0, and Ŵ is the plain two-variable Fourier transform (convention checked against brute-force summation).
- **α is irrelevant up to rescaling the frequency:** Ŵ_α(h,k) = Ŵ_1(αh, αk). So the uniformity in α adds no content.
- **Cube-root symmetry:** K_{m,n}(ζr1, ζ²r2) = K_{m,n}(r1,r2) for ζ³=1, so Ŵ(h,k) = Ŵ(ζ⁻¹h, ζ⁻²k) when p≡1 (mod 3). Exceptional sets Z are therefore unions of such orbits (size 3, except at the origin). This is consistent with a bounded |Z|.
- Case (2) is forced by positivity: if m=m' or n=n', W is a product of |K|² factors, W ≥ 0, so Ŵ(0,0) = Σ W is of order p⁴. The p·1_{(0,0)} term is therefore necessary, not generous.
- The trivial bound is O(p⁴); the "square-root" target is p³ (p² points, p² size each). A4 case (1) says nothing worse than √p·p³ happens on a bounded set. The paper states that the unconditional stratification results give only O(p³) off a curve, O(p^{7/2}) on it, and the trivial bound at a bounded set of points. So A4 differs from the unconditional result in exactly two respects: (a) no exceptional curve in case (1); (b) p^{7/2} instead of p⁴ at the exceptional points. This is stated by the paper; I did not verify it.

**Source-supported but unchecked.**
- Whether this form of A4 is what the Type III argument consumes. The reduction from Ŵ to the Type III bound lives in [22]/[9], not in this manuscript. The manuscript says only that "the sampled theorem of [22] takes A4 as its local input".
- Whether constants existential in (C4,D4,p0) suffice. The paper says they are never used numerically. That is plausible if the constant enters only as C4^{O(ω(q))} = x^{o(1)} over the prime factors of a squarefree modulus q, and the exceptional frequencies contribute D4^{ω(q)} frequencies each at a √p loss. That is my inference. It is not shown in the manuscript. Whether the √q-type loss at exceptional frequencies is affordable in the Type III weighting is decided in [22] and was not checked.
- Faithfulness of the Lean `HasFiniteExceptionalTypeIIIInput` to the displayed A4: one sentence in §7.4 ("constants existential and never used numerically"). Not assessable without the Lean source. Note the Lean name speaks of a "Type III input", while the displayed A4 is a statement about Ŵ; the bridge between the two is not in the paper.

**Unresolved.** Whether the (1)/(2) dichotomy covers every parameter configuration the Type III argument produces, including degenerate coincidences such as m/n = m'/n'. A4 as displayed quantifies over all of them. The paper's Appendix A tests one such tuple per prime.

## 2. Proof dependency (question 2)

**Established, as stated by the paper.** A1 and A3 are Deligne/Katz bounds (Weil II; Katz, Thm 4.1.1). A2 is the 2013 Fouvry–Kowalski–Michel note (8p^{3/2}), proved from Deligne, with a published-in-appendix variant by Birch–Bombieri with unspecified constant; the authors say the note is not refereed.

**Source-supported but unchecked.** The proof of A4 in [9] reportedly combines Laumon's local Fourier transform, Fu's explicit local formulas, purity for perverse sheaves and quantitative sheaf theory (Sawin–Forey–Fresán–Kowalski), and "one new argument excluding Fourier transforms supported on curves". The authors state that this argument has not been refereed, and that no published theorem implies A4. The general stratification (Katz–Laumon, Fouvry–Katz) results give only the weaker conclusion above. That is where the new, unrefereed step enters: it is precisely the passage from "O(p³) off a curve, O(p^{7/2}) on it, trivial at points" to "O(p³) off a bounded set, O(p^{7/2}) on it".

**Where A4 enters this manuscript.** Mathematically (paper's counts, which I recomputed to be internally consistent): of 21,763 Type III parameter choices, 16,243 need only A1–A3 (14,801 meet the literal Polymath criterion; 1,442 more are covered by the 186-paper theorem using A1, A2), and 5,520 need A4 (including 455 that need a "residual-length extension"). Row counts: 13,029+3,149+0+1,772+3,358+455 = 21,763; 2,942+18,821 = 21,763. In Lean, A4 enters once, as a premise of the dense Type III theorems (`TrialSharpDense180.lean`, `TrialRetainedTriple180.lean`), for all their parameter choices. The paper says separating the 16,243 in Lean "would not remove A4 from the final statement". Also, Prop 5.1 and Theorem 5.4 are stated as "Assume A1–A4" and the distribution input is assembled by `SourceSchedule.inputs_of_local_fourier`. Without A4 the best known bound is stated to be 186 [18]; 182 [22] rests on the same A4.

**Unresolved.** Whether the "residual-length extension" used for the 455 choices is part of the theorem of [22] as published, or new in this manuscript. The text reads as the former, but the table lists it as a separate column. Not examined.

## 3. Consequence (question 3)

**Conditionally derived (as claimed, not re-verified by me).** Theorem 1.1: A1–A4 **and** `Numerical` imply H₁ ≤ 180. In Lean: `PrimeGap180.h1_le_180_of_numerical` takes `prime` (A1, A2), `rank4` (A3), `prop31` (A4) and `numerical`, with the three standard axioms only, per the authors. I did not run Lean and did not see the build record.
- The headline is conditional on `Numerical` as well as on A4, which the abstract-level reading can hide. `Numerical` is a 14-field structure. Ten fields are interval-certified; four are existential approximations; the written error analyses (Appendix C) are not machine-checked; some parts are proved in Lean but not substituted into the final theorem. The final margin is about 1.027×10⁻⁶ M (0.09% of the restoration loss), and the authors list several allowances that are tight (0.04%, 0.0037%).
- I found **no place where A4 is silently strengthened** in the text I read: the paper states A4 as an explicit, existential, uniform hypothesis, labels it unrefereed in §1.1, Remark 1.3, §7.3 and §9.2, and says that if it fails Theorem 1.1 "gives no information". Whether the Lean statement is equivalent to the displayed one is unresolved (see §1).
- The use of A4 as a premise for all parameter choices in Lean is **stronger than needed mathematically, but not a stronger hypothesis**: it is the same A4. The reduction from Type III parameter choices to A4 for the 5,520 choices is claimed to be checked in Lean (`TrialSlotSelection180.lean` and generated files); not examined.

## 4. Independent probe (evidence only; not a test of A4)
Python/numpy, double precision, my own implementation of the displayed definitions. Convention, α-rescaling and cube-root symmetry checked first.
- **All tuples, p = 7,11,13,17,19,23,29,31** (α=1, m=1, all n, m', n'; exact reduction by the (r1,r2) scalings, which I derived, not taken from the paper). Case (1): max |Ŵ|/p³ over all tuples and frequencies = 4.62, 3.13, 3.08, 2.57, 6.30, 2.70, 3.36, 4.92. At most one frequency per tuple exceeds 4p³ and at most one exceeds 6p³ (p=19). No line or curve of large values appears. Case (2): ratios grow with p (11→79 p³ by p=31), as expected from the p⁴ term at the origin.
- **Locus m/n = m'/n' (the tuple type in the paper's Appendix A), m=n=1, m'=n'=t, all t, p up to 101; sampled t up to p=199.** For p≡2 (mod 3) the worst case-(1) ratio is 2.5–4.5 (p = 41, 47, 101, 107, 131, 197 sampled). For p≡1 (mod 3) the worst is 4.6–9.6 (p = 37: 9.64; 43: 6.23; 61: 4.64; 67: 6.05; 73: 5.01; 79: 7.11; 97: 7.48; 103: 5.47; 127: 7.22; 151: 5.47; 199: 5.75, the larger primes over 41 sampled t only). In the cases examined in detail (p = 19, 37, 67, 79, 97) the single large value is at the origin (h,k)=(0,0), while the next largest values are about 2–3.4 p³. This is the shape A4(1) allows (one exceptional point). The ratio shows no visible √p growth in this range (0.4–1.6 × √p), but this range cannot distinguish a √p growth with small constant from a bounded constant.
- **What this does and does not show.** The paper's Appendix A reports 2.49–4.22 p³ at p ≥ 101 for three random tuples and one locus tuple per prime. Random tuples miss thin parameter loci. My exhaustive small-prime scan did not find an exceptional curve or a violation of the shape of A4, and the elevated origin value on the locus is the only structure seen. Because C4 and D4 are unspecified and p0 is existential, **no finite computation can confirm or refute A4**; and p ≤ 199 is far below any asymptotic regime. At p=101, √p = 10 and the paper's observed 4.22 leave less than a factor 3 of room, so Appendix A distinguishes little.
- Files: `num/a4test.py`, `num/locus.py`, `num/pt.py`, `num/big.py` in the scratchpad.

## 5. Summary by outcome
- **Established:** exact statement of A4; its well-posedness; α-rescaling; cube-root symmetry; case (2) forced by positivity; internal consistency of the 16,243 / 5,520 / 21,763 counts; paper's own labelling of A4 as unrefereed and of the headline as conditional on A1–A4 and `Numerical`.
- **Conditionally derived:** H₁ ≤ 180 from A1–A4 + `Numerical` (Lean, per the paper; not re-run here).
- **Source-supported but unchecked:** A4's proof in [9]; the A4 → Type III bridge in [22]; the sufficiency of existential constants; Lean–paper faithfulness of A4.
- **Unresolved:** whether the "residual-length extension" is in [22] as published; the √p-loss budget at exceptional frequencies in the Type III weighting; behaviour of Ŵ(0,0) on the locus m/n = m'/n' for p≡1 (mod 3) as p→∞. No defect is claimed for any of them.

## Limits
Algebra and finite computations do not establish A4. The probe is evidence only, at small primes, in floating point. The report does not assess the sheaf-theoretic proof in [9], the Lean source, or Appendices B–C. It was not read by a human specialist.
