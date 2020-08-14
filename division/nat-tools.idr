module nattools

||| Make an isomorphism (of types) Nat to Nat<n + Nat >= n.

||| The natural numbers
--data Nat = Z  | S k

||| Nat < n.


||| Type of evidence for m < n.
||| Exists k:Nat where m+k+1=n.
data LTProof :  (m:Nat) -> (n:Nat) -> Type where
  MkLTProof : (m:Nat) -> (n:Nat) -> (k:Nat) -> plus m (S k) = n -> LTProof m n

||| Type of evidence for  m >= n.
||| Exists k where m = n + k.
data AtLeast : (m:Nat) -> (n:Nat) -> Type where
  MkAtLeast : (m:Nat) -> (n:Nat) -> (k:Nat) -> m = n+k -> AtLeast m n


||| Type of evidence for  n < m xor m >= n
data SplitNatProof : (m:Nat) -> (n:Nat) -> Type where
  Below : (m,n:Nat) -> LTProof m n -> SplitNatProof m n
  Above : (m,n:Nat) -> AtLeast m n -> SplitNatProof m n




hole_1 : (m : Nat) -> (k : Nat) -> (e : plus m (S k) = n) -> plus (S m) (S k) = S n

monotoneSplit : SplitNatProof m n -> SplitNatProof (S m) (S n)
monotoneSplit (Below m n (MkLTProof m n k e))  = Below (S m) (S n) (MkLTProof (S m) (S n) k (hole_1 m k e) )
monotoneSplit (Above m n x)  = ?hole_2


||| Split Lemma: For every m:Nat every n:Nat, m < n or m >= n, exclussively
split : (m:Nat) -> (n:Nat) -> SplitNatProof m n
split m Z = Above m 0 (MkAtLeast m 0 m Refl)
split Z (S k) = Below Z (S k) (MkLTProof 0  (S k) k Refl)
split (S j) (S k) = let x = split j k in (monotoneSplit x)
