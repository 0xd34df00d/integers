module Z.Grothendieck

import Data.So
import Data.List.Views
import Z.Interface

%default total

data ZTy : Type where
  MkZ : (m, n : Nat) -> ZTy

ZInt ZTy where
  zz = MkZ 0 0
  zs (MkZ m n) = MkZ (S m) n

data Equiv : ZTy -> ZTy -> Type where
  MkEquiv : (prf : m1 + n2  = m2 + n1) -> Equiv (MkZ m1 n1) (MkZ m2 n2)

zeroEquiv : (n : Nat) -> MkZ n n `Equiv` MkZ 0 0
zeroEquiv n = MkEquiv $ plusZeroRightNeutral n

sEquiv : (n, m : Nat) -> MkZ (S n) (S m) `Equiv` MkZ n m
sEquiv n m = MkEquiv $ plusSuccRightSucc n m

data ZSign : ZTy -> Type where
  ZZero : (prf : n = m)    -> ZSign (MkZ m n)
  ZPos  : (prf : n `LT` m) -> ZSign (MkZ m n)
  ZNeg  : (prf : m `LT` n) -> ZSign (MkZ m n)

lteNotEqImpliesLT : (m, n : Nat) -> (ltePrf : m `LTE` n) -> (notEqPrf : Not (m = n)) -> m `LT` n
lteNotEqImpliesLT Z Z     _ notEqPrf = absurd $ notEqPrf Refl
lteNotEqImpliesLT Z (S n) _ _        = LTESucc LTEZero
lteNotEqImpliesLT (S m) (S n) (LTESucc ltePrf) notEqPrf = LTESucc $ lteNotEqImpliesLT m n ltePrf (notEqPrf . cong)

sign : (k : ZTy) -> ZSign k
sign (MkZ m n) with (S n `isLTE` m, m `decEq` n)
  | (Yes prf, _) = ZPos prf
  | (_, Yes eq) = ZZero $ sym eq
  | (No contra, No eqContra) = ZNeg $ lteNotEqImpliesLT _ _ (notLTImpliesGTE contra) eqContra

VerifiedSucc ZTy where
  EqZ = Equiv
  succInjective (MkZ m1 n1) (MkZ m2 n2) (MkEquiv prf) = MkEquiv $ succInjective _ _ prf
  succSurjective (MkZ m n) = (MkZ m (S n) ** MkEquiv $ plusSuccRightSucc m n)

VerifiedZInt ZTy where
  induction prf0 prfStep (MkZ m n) with (sign $ MkZ m n)
    induction prf0 prfStep (MkZ n n)     | (ZZero Refl)         = prf0 _ (zeroEquiv n)
    induction prf0 prfStep (MkZ (S m) n) | (ZPos (LTESucc prf)) =
      let
        rec = prfStep (zp $ MkZ (S m) n)
      in ?rhs
    induction prf0 prfStep (MkZ m (S n)) | (ZNeg (LTESucc prf)) = ?rhs
