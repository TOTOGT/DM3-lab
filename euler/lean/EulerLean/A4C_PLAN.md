# Plan: Hecke recurrence on Y_p, stages A4c and A4d (2026-11-19)

STATUS: plan only, hand-derived. No Lean written for A4c/A4d. Nothing here is proved in Lean beyond what is cited.

## What already exists (Stage80a chain, kernel-checked, standard axioms)
- `Section75b.gen_exists`: for each key k (p+1 of them) the right ideal `Ik k` is `g_k * H` with N(g_k) = p.
- `Section78a.ncard_Ik_Hn`: the elements of norm p*m in `Ik k` are exactly `g_k * b`, b of norm m (bijection b -> g_k * b).
- `Section78b.count_pairs`: sum over k of those counts = h(pm) + p * #{x in Hn(pm) : red x = 0}.
- `Section78c.zero_count`: {x in Hn(pm) : red x = 0} = p * Hn(m/p) if p | m, else empty.
- `Section76b.Ik_existsUnique`: for x of norm pm with red x != 0 there is exactly one k with x in Ik k.
- A4a/A4b (this session): `TY`, `TY_adjoint`, `Hm`, `aH`, `aH_rmul`, `Tm_adjoint`.

## Two primes (naming, to avoid a clash)
- `l` : the Hecke prime (the "p" of Stage78). It carries the keys, the ideals `Ik`, and the reduction mod l.
- `p` : the level prime of Y_p = Gamma\PGL2(F_p) (the "p" of A4a/A4b). Require l != p, l odd, p odd, so the reduction mod p of g_k is invertible.

## A4c: the counting identity, as an identity of sums over quaternions (no group, no quotient)
Fix l, keys k with generators g_k. For any Phi : Quaternion Q -> C and m:

  sum_k sum_{b in Hn m} Phi(g_k * b)  =  sum_{x in Hn(l m)} Phi(x)  +  l * sum_{y in Hn(m/l)} Phi(l * y)

(the last sum is 0 when l does not divide m).

Hand derivation. The left side is a sum over pairs (k, b). By `ncard_Ik_Hn` the map (k, b) -> g_k * b is a bijection from {k} x Hn m onto the disjoint-by-k union of the sets {x in Hn(lm) : x in Ik k}. An element x of norm lm with red x != 0 lies in exactly one Ik (Ik_existsUnique); an element with red x = 0 is l*y (zero_red_form) and lies in all l+1 of them. So the left side counts x once, plus l extra times when red x = 0: the right side. This is `count_pairs` with the counting measure replaced by the weight Phi, i.e. a weighted version of the Stage78b double count. The cardinality version is the special case Phi = 1.

New Lean content: restate the Stage78b double count with a weight Phi (a Finset.sum_comm over (k, x) instead of ncard), plus the identification of the zero-reduction fibre with `l * Hn(m/l)`. No new algebra.

## A4d: the operator statement
Let rho_p : Hurwitz elements of norm prime to p -> PGL2(F_p) be the reduction (A4b's `aH`). For f on Y_p put

  (U_m f)(Gamma g) = sum_{b in Hn m} f(Gamma rho(b) g)             -- A4b's TY with a = aH, unnormalised (24 sigma(m) terms)
  (V_l f)(Gamma g) = sum_k f(Gamma rho(g_k) g)                       -- l+1 terms, one per key

Then, for l != p, l ∤ p, and p ∤ m:

  U_m (V_l f) = U_{lm} f + l * U_{m/l} f      (last term absent if l does not divide m)

because rho(g_k * b) = rho(g_k) rho(b) and rho(l * y) = rho(l) rho(y) with rho(l) a scalar, which is trivial in PGL2. Well-definedness of V_l in the choice of generator g_k: replacing g_k by g_k u (u a unit) reindexes b -> u b inside U_m, and Hn m is closed under left multiplication by units, so the composite does not depend on it. V_l on its own is not obviously well defined on Y_p (it is the l+1 term operator normalised so that U_l = 24 V_l on the nose: each class of Hn l under left units has 24 members). A4d should therefore state the identity for the composite U_m V_l and, as a corollary, for U_m U_l = 24 (U_{lm} + l U_{m/l}).

## What this does NOT give
- Commutation U_m U_n = U_n U_m (needs the same identity with the primes in either order, plus multiplicativity for coprime m, n).
- Eigenvalue bounds, the size 24 sigma(m), or H31gt3. Those are later stages.

## Risks, in order
1. The reindexing/well-definedness step in A4d (units acting on the left of Hn m): small but fiddly with `Quotient.out`.
2. Fibre/sum interchange over `Option (ZMod l)` and `Hn`: use `Finset.sum_comm` over Finsets built from `Hn_finite`; mirrors count_pairs.
3. Keeping `l` and `p` as different Fact primes through the namespaces: use `l` for Sections 75-78 imports and `p` for A4a/A4b.
