module ZInt.Interface

%default total

%access public export

interface ZInt ty where
  zz : ty
  zs : ty -> ty
  zp : ty -> ty

interface ZInt ty => VerifiedZInt ty where
  succInjective  : (k1, k2 : ty) -> (zs k1 = zs k2) -> k1 = k2
  succSurjective : (k : ty) -> (k' ** zs k' = k)
  succPredId     : (k : ty) -> (zs (zp k) = k)
