module Z.Grothendieck

import Z.Interface

%default total

data ZTy : Type where
  MkZ : (m, n : Nat) -> ZTy

ZInt ZTy where
  zz = MkZ 0 0
  zs (MkZ m n) = MkZ (S m) n

data Equiv : ZTy -> ZTy -> Type where
  MkEquiv : (prf : m1 + n2  = m2 + n1) -> Equiv (MkZ m1 n1) (MkZ m2 n2)

VerifiedSucc ZTy where
  EqZ = Equiv
  succInjective (MkZ m1 n1) (MkZ m2 n2) (MkEquiv prf) = MkEquiv $ succInjective _ _ prf
  succSurjective (MkZ m n) = (MkZ m (S n) ** MkEquiv $ plusSuccRightSucc m n)

VerifiedZInt ZTy where
  induction prf0 prfStep (MkZ m n) = ?rhs
