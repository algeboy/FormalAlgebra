module nat.split


||| The type of evidence I'll accept for m < n:
||| some k and evidence for m+(k+1)=n
data LTProof : Nat -> Nat -> Type where
     MkLTProof : (m:Nat) -> (n:Nat) -> (k:Nat) -> (m+(k+1)=n) -> LTProof m n


||| The type of evidence I'll accept for m < n:
||| some k and evidence for m+(k+1)=n
data GTEProof : Nat -> Nat -> Type where
    MkGTEProof : (m:Nat) -> (n:Nat) -> (k:Nat) -> (m=n+k) -> GTEProof m n

data SplitNatProof : Nat -> Type where
  Below : LTProof m n -> SplitNatProof n
  Above : GTEProof m n -> SplitNatProof n

||| Take (m,n) and return either proof that m <n or proof that m>=n
split : (m:Nat) -> (n:Nat) -> SplitNatProof n
split Z n = Below (MkLTProof n n n ?hole_3)
split (S k) n = ?hole_2
--split m Z = Above MkGTEProof m Z m refl
--split Z S k = Below MkLTProof Z S k k refl

--SplitNat : (n:Nat) -> DPair Nat (SplitNatProof n)
