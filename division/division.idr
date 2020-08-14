|||
||| A type-checkable division algorithm.
|||
||| CC-BY 2020 James B. Wilson 
||| Department of Mathematics 
||| Colorado State University
|||

data LT = {m:Nat} ->  (n:Nat) ->  Type
mkLessThan : {m:Nat} -> (n:Nat) -> (k:Nat) -> (e:n+k+1=m) -> LessThan m

data GTE = {m:Nat} ->  (n:Nat) ->  Type
mkGreaterThanEqual : {m:Nat} -> (n:Nat) -> (k:Nat) -> (e:n=m+k) -> GTE m


||| Proposition: For all positive natural numbers m and all natural numbers n,
||| there exists a natural number q, and natural number r < m, such that n=qm+r.
div :  (m:Nat) -> (n:Fin m) -> (q:Nat ** (r:Nat ** (n=(q*m+r+q)))
div m n = (Z ** (n ** Refl))
div m n = lift (div m n-m) where lift (q**(r**e)) = ((q+1)**(r**cong {f} e)))  



---div S(m) n:Fin m = (q,n, refl:n=n)
---div S(m) n       = (1+q,r, cong(e):n=q*S(m)+r) where (q,r,e) = div(S(m),n-m)
