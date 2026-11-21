

/-! Definitions for the kernel-checked finite certificate (see EDcert.lean). Computation only; no theorems. -/

namespace EDcert

def W : Nat := 65536
def g0 (c : Nat) : Nat := if c = 0 then 0 else c * W - 320
def Lg (c : Nat) : Nat := c * W + W - g0 c

def isqrtA : Nat → Nat → Nat → Nat
  | 0, _, r => r
  | f+1, n, r => if (r + n / r) / 2 < r then isqrtA f n ((r + n / r) / 2) else r
def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtA 80 n (2 ^ (Nat.log2 n / 2 + 1))
def csqrt (t : Nat) : Nat := if isqrt t * isqrt t = t then isqrt t else isqrt t + 1

def stepY (x a L : Nat) (m y : Nat) : Nat :=
  if Nat.gcd x y = 1 ∧ (x + y) % 2 = 1 ∧ a ≤ x * x + y * y ∧ x * x + y * y < a + L then
    m ||| (1 <<< (x * x + y * y - a)) else m

def rowMask (a L x : Nat) : Nat :=
  if a + L ≤ x * x then 0 else
  let ylo := if a ≤ x * x then 0 else csqrt (a - x * x)
  let yhi := min x (isqrt (a + L - 1 - x * x))
  (List.range' ylo (yhi + 1 - ylo)).foldl (stepY x a L) 0

def xsL (a L : Nat) : List Nat := List.range' (isqrt (a / 2)) (isqrt (a + L) + 2 - isqrt (a / 2))

def Gm (c : Nat) : Nat := (xsL (g0 c) (Lg c)).foldl (fun m x => m ||| rowMask (g0 c) (Lg c) x) 0

def candCert : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (1, 4), (3, 4), (2, 5), (1, 6), (4, 5), (2, 7), (5, 6), (1, 8), (3, 8), (2, 9), (5, 8), (4, 9), (1, 10), (3, 10), (7, 8), (2, 11), (4, 11), (1, 12), (7, 10), (6, 11), (5, 12), (2, 13), (9, 10), (4, 13), (7, 12), (1, 14), (3, 14), (5, 14), (2, 15), (8, 13), (4, 15), (1, 16), (3, 16), (10, 13), (9, 14), (5, 16), (8, 15), (2, 17), (4, 17), (12, 13)]
def candsL : List Nat := candCert.map (fun p => p.1 * p.1 + p.2 * p.2)

def cover (c : Nat) : Nat := candsL.foldl (fun m a => m ||| (Gm c <<< a)) 0

def tgt (c : Nat) : Nat := (List.range (W / 4)).foldl (fun m i => m ||| (1 <<< (c * W - g0 c + 2 + 4 * i))) 0

def chunkOk (c : Nat) : Bool := (cover c &&& tgt c) == tgt c

end EDcert
