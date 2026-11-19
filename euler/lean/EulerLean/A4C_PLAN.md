# Plan: Hecke recurrence on Y_p, stages A4c and A4d (2026-11-19, corrected after A4c compiled)

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

## Correction (after A4c compiled; supersedes the V_l discussion above)
STATUS: A4c is DONE (StageA4c.lean, CI run 44634468552 green, standard axioms). The text above about V_l was wrong in one respect.

- `V_l f (Gamma g) = sum_k f(Gamma rho(g_k) g)` (one generator per key) is NOT well defined on Y_p. TY_mk needs right-stability of the family: for gamma = rho(u) in Gamma there must be a permutation pi with rho(g_{pi k}) = delta * rho(g_k) * gamma and delta in Gamma. Replacing g_k by g_k u changes rho(g_k) on the right by rho(u), which is fine for gamma-stability only if the family contains BOTH g_k and g_k u. A single generator per key does not.
- Fix: use the full family Hn l (all 24(l+1) elements, the A4b `aH` family at index l), i.e. U_l. Then the unit reindexing is exactly A4b's `aH_stable` (right multiplication by a unit permutes Hn l) and needs no new work.

Corrected A4d statement, for primes l != p, p not dividing l*m:
  U_m (U_l f) = 24 * ( U_{l m} f + l * U_{m/l} f )        (last term absent unless l | m)
where U_n f (Gamma g) = sum over alpha in Hn n of f(Gamma rho(alpha) g)  (A4b `TY` with `aH`, unnormalised).

Derivation. By TY_mk twice, (U_m (U_l f))(Gamma g) = sum_{b in Hn m} sum_{c in Hn l} Phi(c b) with Phi(x) = f(Gamma rho(x) g). Hn l = { g_k u : k a key, u a unit } with 24 u per key (gens_count), so the sum is sum_u sum_k sum_b Phi(g_k u b). Reindex b -> u b (left multiplication by a unit permutes Hn m): it equals 24 * sum_k sum_b Phi(g_k b). Now apply A4c `hecke_count`, and use rho(l y) = rho(y) (l is a scalar in PGL2).

New work, in order: (1) Hn l = disjoint union over keys of g_k * units (Gens, `gens_count`, `Ik_existsUnique`-style uniqueness of the key); (2) left-unit reindexing of Hn m (a `lmul` analogue of A4b `rmul`); (3) rho multiplicative on the relevant pairs (`red_mul`, with two different reductions: mod l for the keys, mod p for rho); (4) `Hm` (subtype, Fintype) versus `Hn` (Set, Finset via Hn_finite): one bridging lemma; (5) assemble. Most likely a two-stage split: A4d = (1)(2) as an identity of finite sums over quaternions, A4e = (3)(4)(5) on Y_p.
