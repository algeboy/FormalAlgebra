module nattools

%default total

||| Make an isomorphism (of types) Nat to Nat<n + Nat >= n.

||| The natural numbers
--data Nat = Z  | S k


|||----------------------------------------------------------------------------
||| Nat < n.


||| Type of evidence for m < n.
||| Exists k:Nat where m+k+1=n.
data LTProof :  (m:Nat) -> (n:Nat) -> Type where
  MkLTProof : (m:Nat) -> (n:Nat) -> (k:Nat) -> plus m (S k) = n -> LTProof m n

|||-----------------------------------------------------------------------------
||| Nat >= n

||| Type of evidence for  m >= n.
||| Exists k where m = n + k.
data AtLeast : (m:Nat) -> (n:Nat) -> Type where
  MkAtLeast : (m:Nat) -> (n:Nat) -> (k:Nat) -> m = n+k -> AtLeast m n

|||-----------------------------------------------------------------------------
||| Nat -> Nat<n + Nat >= n

||| Type of evidence for  n < m xor m >= n
data SplitNatProof : (n:Nat) -> Type where
  Below : (n:Nat) -> (m:Nat) -> LTProof m n -> SplitNatProof n
  Above : (n:Nat) -> (m:Nat) -> AtLeast m n -> SplitNatProof n


||| have m+(S k)=n  and need (S m)+(S k)=S n
||| Cong {S} e : S ( m + (S k)) = S n  but need to rewrite, LHS.
||| Note, cong will implicitly find the S to apply to both sides by types it
||| has to match.
|||
||| by Plus associative we have (S m) + (S k)= S( m+ (S k))
||| we also have S(m+(S k))=S n
||| By transitivity we get (S m) + (S k) = S n
monotoneBelow : (m : Nat) -> (k : Nat) -> (e : plus m (S k) = n) -> plus (S m) (S k) = S n
monotoneBelow m k e = trans (plusAssociative 1 m (S k)) (cong e)

monotoneAbove : (n : Nat) -> (k : Nat) -> (e : m = (n + k)) -> S m = ((S n) + k)
monotoneAbove n k e = trans (cong e) Refl

monotoneSplit : SplitNatProof n -> SplitNatProof (S n)
monotoneSplit (Below n m (MkLTProof m n k e))  = Below (S n) (S m) (MkLTProof (S m) (S n) k (monotoneBelow m k e))
monotoneSplit (Above n m (MkAtLeast m n k e))  = Above (S n) (S m) (MkAtLeast (S m) (S n) k (monotoneAbove n k e))


||| Split Lemma: For every m:Nat every n:Nat, m < n or m >= n, exclussively
natsSplit : (n:Nat) -> (m:Nat) -> SplitNatProof n
natsSplit Z m = Above 0 m (MkAtLeast m 0 m Refl)
natsSplit (S k) Z = Below (S k) Z (MkLTProof 0  (S k) k Refl)
natsSplit (S k) (S j) = let x = natsSplit k j in (monotoneSplit x)
